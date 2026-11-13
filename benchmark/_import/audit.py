#!/usr/bin/env python3
"""Validate the imported corpora and write `data/_manifest.json`.

Checks, per problem, that the oracle behaves as the source labels claim:
buggy programs must fail at least one test, and the paired accepted program
(`fixed/`) or the instructor reference must pass all of them. Programs that do
not parse are flagged rather than silently dropped: PyDex's corpus is entirely
syntax errors by construction, so a flag is information, not an error.

The manifest is what later phases read, so a corrupt record never reaches a
builder unnoticed.

Usage:  python data/_import/audit.py [--sample N] [--jobs K]
"""
from __future__ import annotations

import argparse
import ast
import json
import random
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from src.runner.testing import run_tests  # noqa: E402

DATA = Path("data")


def parses(src: str) -> bool:
    try:
        ast.parse(src)
        return True
    except SyntaxError:
        return False


def audit_problem(pid: str, sample: int, timeout: float) -> dict:
    pdir = DATA / pid
    problem = json.loads((pdir / "problem.json").read_text())
    bugs = sorted((pdir / "buggy").glob("*.py"))
    rng = random.Random(7)
    checked = bugs if sample <= 0 or len(bugs) <= sample else rng.sample(bugs, sample)

    bad_syntax_buggy = sum(1 for b in bugs if not parses(b.read_text()))
    fixed_dir = pdir / "fixed"
    bad_syntax_fixed = 0
    if fixed_dir.is_dir():
        bad_syntax_fixed = sum(1 for f in fixed_dir.glob("*.py")
                               if not parses(f.read_text()))

    fails = oracle_ok = 0
    for b in checked:
        if not run_tests(b.read_text(), problem, timeout=timeout, stop_early=True).all_pass:
            fails += 1
    # reference / paired fix must pass
    ref_checked = ref_pass = 0
    if (pdir / "reference.py").exists():
        ref_checked = 1
        ref_pass = int(run_tests((pdir / "reference.py").read_text(), problem,
                                 timeout=timeout).all_pass)
    elif fixed_dir.is_dir():
        for b in checked:
            f = fixed_dir / b.name
            if not f.exists() or not parses(f.read_text()):
                continue
            ref_checked += 1
            ref_pass += int(run_tests(f.read_text(), problem, timeout=timeout).all_pass)
    else:
        # no reference/fix pairing: sample the correct/ pool as the oracle
        correct = sorted((pdir / "correct").glob("*.py"))
        if correct:
            samp = correct if len(correct) <= sample else rng.sample(correct, sample)
            for c in samp:
                ref_checked += 1
                ref_pass += int(run_tests(c.read_text(), problem, timeout=timeout).all_pass)
    return {
        "pid": pid, "source": problem.get("source"), "mode": problem.get("mode"),
        "tests": len(problem.get("tests", [])), "buggy": len(bugs),
        "correct": len(list((pdir / "correct").glob("*.py"))) if (pdir / "correct").is_dir() else 0,
        "fixed": len(list(fixed_dir.glob("*.py"))) if fixed_dir.is_dir() else 0,
        "buggy_syntax_errors": bad_syntax_buggy,
        "fixed_syntax_errors": bad_syntax_fixed,
        "checked": len(checked), "buggy_actually_fail": fails,
        "oracle_checked": ref_checked, "oracle_pass": ref_pass,
    }


def _job(a):
    return audit_problem(*a)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", type=int, default=5,
                    help="buggy programs to execute per problem (0 = all)")
    ap.add_argument("--timeout", type=float, default=15.0)
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()

    pids = sorted(p.name for p in DATA.iterdir()
                  if p.is_dir() and (p / "problem.json").exists())
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        rows = list(ex.map(_job, [(p, args.sample, args.timeout) for p in pids]))

    (DATA / "_manifest.json").write_text(json.dumps(
        {"problems": rows}, indent=1))

    for src in sorted({r["source"] for r in rows if r["source"]}):
        sel = [r for r in rows if r["source"] == src]
        if not sel:
            continue
        chk = sum(r["checked"] for r in sel)
        print(f"[{src}] {len(sel)} problems, {sum(r['buggy'] for r in sel)} buggy")
        print(f"  buggy actually fail : {sum(r['buggy_actually_fail'] for r in sel)}/{chk}")
        print(f"  oracle passes       : {sum(r['oracle_pass'] for r in sel)}/"
              f"{sum(r['oracle_checked'] for r in sel)}")
        print(f"  syntax errors       : buggy {sum(r['buggy_syntax_errors'] for r in sel)}, "
              f"fixed {sum(r['fixed_syntax_errors'] for r in sel)}")
        bad = [r["pid"] for r in sel if r["checked"] and r["buggy_actually_fail"] < r["checked"]]
        if bad:
            print(f"  !! problems where some buggy programs PASS: {bad[:10]}")
    print(f"\nwrote {DATA / '_manifest.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
