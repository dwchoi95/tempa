"""What the static semantics catches that the engine's per-candidate checks do not. Every rule of the 106 final rule
files that the semantics rejects is compiled with its checks off, the engine's checks kept, and applied to every buggy
program of its assignment.
    python3 -I static_off.py REPO   -> static_off.txt, static_off.jsonl (each surviving candidate)"""
import ast, glob, importlib.util, json, re, signal, sys, types
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core import rulelang as L                 # noqa: E402
HERE = Path(__file__).resolve().parent
src = (REPO / "src/core/rulelang.py").read_text()
OFF = [('        raise RuleError("a definition (def or class) is never a hole")\n', '        pass\n'),
       ('            raise RuleError("a pattern matches one expression, one statement, or two or three statements")\n', '            pass\n')]
for a, b in OFF:
    assert src.count(a) == 1, a
    src = src.replace(a, b)
O = types.ModuleType("rulelang_off"); O.__dict__["__name__"] = "rulelang_off"
sys.modules["rulelang_off"] = O
exec(compile(src, "rulelang_off", "exec"), O.__dict__)
O._static = lambda r, bound: None

REASONS = [("unbound name", r"come from neither the match nor builtins"), ("unbound metavariable", r"uses unbound \$"),
           ("changes nothing", r"changes nothing"), ("return dropped", r"must keep a return"),
           ("definition as hole", r"definition \(def or class\)"), ("hole size", r"a pattern matches one"),
           ("does not parse or other", r".")]


def reason(e):
    return next(n for n, p in REASONS if re.search(p, e))


def job(f):
    pid, model = Path(f).parts[-3], Path(f).parts[-2]
    progs = sorted((REPO / "benchmark" / pid / "buggy").glob("*.py"))
    c, rows = Counter(), []
    for b in re.split(r"(?m)^(?=rule )", Path(f).read_text()):
        if not b.strip().startswith("rule "):
            continue
        try:
            L.compile_rule(b)
            continue
        except L.RuleError as e:
            why = reason(str(e)); msg = str(e)
        except RecursionError:
            continue
        c[why, "rejected"] += 1
        try:
            r = O.compile_rule(b)
        except Exception:                          # noqa: BLE001 - it cannot run at all
            c[why, "cannot compile"] += 1
            continue
        got = 0
        for g in progs:
            s = g.read_text()
            signal.alarm(20)
            try:
                cs = r.apply(s)
            except Exception:                      # noqa: BLE001
                c[why, "raised"] += 1
                continue
            finally:
                signal.alarm(0)
            for q in cs:
                got += 1
                rows.append(dict(pid=pid, model=model, rule=r.name, why=why, buggy=g.stem, patch=q, msg=msg[:120], tool=str(Path(f).relative_to(REPO))))
        c[why, "rules with a candidate"] += got > 0
        c[why, "candidates"] += got
    return c, rows


def alarm(*_):
    raise TimeoutError


def init():
    signal.signal(signal.SIGALRM, alarm)


if __name__ == "__main__":
    files = sorted(f for f in glob.glob(str(REPO / "tools" / "**" / "fixer.rules"), recursive=True)
                   if "/select_rand/" not in f)   # the 106 TRL tools: main, rebuilds, splits
    tot, out = Counter(), []
    with Pool(12, initializer=init) as p:
        for c, rows in p.imap_unordered(job, files):
            tot.update(c); out += rows
    with (HERE / "static_off.jsonl").open("w") as w:
        for r in out:
            w.write(json.dumps(r) + "\n")
    txt = [f"{len(files)} files"] + [f"{k}: {v}" for k, v in sorted(tot.items(), key=str)]
    print("\n".join(txt)); (HERE / "static_off.txt").write_text("\n".join(txt) + "\n")
