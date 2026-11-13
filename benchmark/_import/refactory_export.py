"""Export Codeforces problems into the Refactory tool's data format.

Follows the prior-work convention for judge-style corpora: each submission is
placed **verbatim** under ``def main():`` — no hoisting, no renaming, no body
restructuring — so buggy and correct programs keep identical shape and match
each other function-by-function (``main`` vs ``main``), with original module
scoping preserved naturally by closures.

What the executor still makes impossible without help (verified empirically
against their code):

* every ``import`` line is stripped by their regularizer, even indented ones —
  ``code/global.py`` (read raw, never regularized) supplies the modules and the
  common bare names (``gcd``, ``itemgetter``, ...);
* there is no stdin — ``global.py``'s ``_feed`` installs a per-test
  ``io.StringIO`` as the real ``sys.stdin`` (so ``sys.stdin.readline()`` etc.
  work untouched) and shims ``input``/``print``/bare ``stdin``/``stdout``;
* ``SystemExit`` kills their runner thread — ``exit``/``quit`` are shimmed to a
  catchable exception and ``sys.exit`` is textually pointed at the shim;
* programs whose source defines a function become nested-``def`` after the
  wrap; their hole-injection then produces uncompilable code (verified), so
  such programs fail all tests under Refactory. That is the convention's known
  cost (~14% of buggy here) and is reported, not hidden.

Only three mechanical textual rewrites are applied (uniformly, to every
program): ``sys.exit -> exit``, ``__name__ == '__main__' -> True``,
``sys.stdout.write -> _wout`` (+ ``sys.stdout.flush() -> None``).

Comparison oracle: expected outputs are normalized to a single token stream
(exactly our judge's whitespace-insensitive comparison) and written as
``repr``; the shims' ``_flush`` emits the program's collected output the same
way, so both systems face one oracle.

Two port-robustness patches to the tool itself (algorithm untouched), both in
``basic_framework/exec.py``: (1) its RLIMIT_AS call is wrapped in try/except
(macOS refuses that limit and the tool otherwise crashes at import); (2) its
thread-join loop waits a bounded grace after the per-test timeout instead of
forever — a candidate whose code swallows their StopException via a bare
``except:`` could otherwise hang the entire tool; such a test now scores as
failed, as on any judge.

Usage:  python3 data/_import/refactory_export.py cf_125A [--wrong-limit N]
Writes: baselines/refactory/data_cf/<pid>/{ans,code/{reference,correct,wrong}}
"""
from __future__ import annotations

import argparse
import ast
import io
import json
import re
import signal
import sys
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

GLOBAL_PY = '''\
import io as _io
import sys
import math, re, string, itertools, functools, operator, heapq, bisect, array
import collections, copy, os, random
from collections import Counter, defaultdict, deque, OrderedDict
from math import gcd, sqrt, ceil, floor, factorial, log, log2, inf, pi, isqrt, comb
from itertools import permutations, combinations, product, accumulate, groupby, chain
from functools import reduce, lru_cache, cmp_to_key
from heapq import heappush, heappop, heapify, heappushpop, nlargest, nsmallest
from bisect import bisect, bisect_left, bisect_right, insort
from operator import itemgetter


class _Exit(Exception):
    pass


def exit(*a):
    raise _Exit()


quit = exit
_OUT = []


class _W:                       # shim for bare `stdout` (from sys import stdout)
    def write(self, x):
        _OUT.append(str(x))
        return len(str(x))

    def flush(self):
        pass


stdout = _W()
_wout = stdout.write


def print(*a, **k):
    _OUT.append(str(k.get("sep", " ")).join(map(str, a)))


_SIN = _io.StringIO("")
stdin = _SIN


def input(*a):
    return _SIN.readline().rstrip("\\n")


def _feed(s):
    global _SIN, stdin
    _OUT.clear()
    _SIN = _io.StringIO(s)
    stdin = _SIN
    sys.stdin = _SIN


def _flush(*a):
    sys.stdout.write(" ".join("\\n".join(_OUT).split()) + "\\n")
'''


def _rewrite(src: str) -> str:
    """The three mechanical rewrites the executor makes unavoidable."""
    src = src.replace("sys.stdout.write", "_wout")
    src = src.replace("sys.stdout.flush()", "None")
    src = src.replace("sys.exit", "exit")
    src = re.sub(r"__name__\s*==\s*['\"]__main__['\"]", "True", src)
    return src


def wrap(source: str) -> str | None:
    """Whole submission verbatim under ``def main():`` (prior-work convention)."""
    try:
        ast.parse(source)
    except SyntaxError:
        return None
    body = _rewrite(source)
    indented = "\n".join("        " + l if l.strip() else l
                         for l in body.splitlines()) or "        pass"
    out = f"def main():\n    try:\n{indented}\n    except _Exit:\n        pass\n"
    try:
        compile(out, "<wrapped>", "exec")
    except SyntaxError:
        return None
    return out


def has_def(source: str) -> bool:
    """Programs defining functions cannot survive their hole injection."""
    try:
        return any(isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
                   for n in ast.walk(ast.parse(source)))
    except SyntaxError:
        return False


def _entry(stdin_text: str) -> str:
    return f"_feed({stdin_text!r}) ; main() ; _flush() #print("


def _norm(text: str) -> str:
    return " ".join(text.split())


class _Alarm(Exception):
    pass


def simulate(wrapped: str, stdin_text: str, expected: str, timeout: float = 3.0) -> bool:
    """Mimic Refactory's exec pipeline (sans hole injection) for one test."""
    final = GLOBAL_PY + "\n\n" + wrapped + "\n\n" + _entry(stdin_text)
    buf = io.StringIO()
    real_stdin = sys.stdin
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(_Alarm()))
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        with redirect_stdout(buf):
            exec(final, {})                            # noqa: S102 - data prep
    except (_Alarm, Exception):                        # noqa: BLE001
        return False
    except BaseException:                              # SystemExit etc.
        return False
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        sys.stdin = real_stdin
    return buf.getvalue() == _norm(expected) + "\n"


def export(pid: str, wrong_limit: int = 0, sim_tests: int = 3) -> None:
    prob = json.loads((ROOT / "data" / pid / "problem.json").read_text())
    tests = prob["tests"]
    out = ROOT / "baselines" / "refactory" / "data_cf" / pid
    (out / "ans").mkdir(parents=True, exist_ok=True)
    for sub in ("reference", "correct", "wrong", "fail"):
        (out / "code" / sub).mkdir(parents=True, exist_ok=True)
    (out / "code" / "global.py").write_text(GLOBAL_PY)

    for i, t in enumerate(tests, 1):
        (out / "ans" / f"input_{i:03d}.txt").write_text(_entry(t["stdin"]))
        (out / "ans" / f"output_{i:03d}.txt").write_text(repr(_norm(t["expected"])))

    stats = {"correct_ok": 0, "correct_unadaptable": 0,
             "wrong_ok": 0, "wrong_unadaptable": 0}
    sample = tests[:sim_tests]

    # correct pool: EVERY wrappable correct solution, identical to TEMPA's pool
    # (only unparseable sources cannot be wrapped at all).
    corr_dir = ROOT / "data" / pid / "correct"
    ref_candidates = []
    for f in sorted(corr_dir.glob("*.py")):
        src = f.read_text()
        w = wrap(src)
        if w is None:
            stats["correct_unadaptable"] += 1
            continue
        (out / "code" / "correct" / f.name).write_text(w)
        stats["correct_ok"] += 1
        # the reference anchor must actually run under their executor
        if not has_def(src) and all(simulate(w, t["stdin"], t["expected"])
                                    for t in sample):
            ref_candidates.append(f)

    kept = sorted((out / "code" / "correct").glob("*.py"),
                  key=lambda p: len(p.read_text()))
    if not kept:
        raise SystemExit(f"{pid}: no adaptable correct solutions")
    anchor = (sorted(ref_candidates, key=lambda p: len(p.read_text()))[0]
              if ref_candidates else kept[0])
    (out / "code" / "reference" / "reference.py").write_text(
        (out / "code" / "correct" / anchor.name).read_text()
        if ref_candidates else kept[0].read_text())

    wrong_dir = ROOT / "data" / pid / "buggy"
    files = sorted(wrong_dir.glob("*.py"))
    if wrong_limit:
        files = files[:wrong_limit]
    for f in files:
        src = f.read_text()
        w = wrap(src)
        if w is None:
            stats["wrong_unadaptable"] += 1
            continue
        (out / "code" / "wrong" / f.name).write_text(w)
        stats["wrong_ok"] += 1

    print(f"[{pid}] tests={len(tests)}  {stats}  reference={anchor.name if ref_candidates else kept[0].name}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("pids", nargs="+")
    ap.add_argument("--wrong-limit", type=int, default=0)
    args = ap.parse_args()
    for pid in args.pids:
        export(pid, wrong_limit=args.wrong_limit)
