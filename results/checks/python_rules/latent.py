"""Accepted repairs that read a name nothing binds, which the buggy program did not: a NameError on
any input that reaches the read, in a program every test passed. Per arm, from the stored logs.
    python3 -I latent.py REPO   -> latent.txt"""
import ast, builtins, csv, sys
from collections import Counter
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.experiments._common import ORDER          # noqa: E402
HERE = REPO / "results/checks/python_rules"
BI = set(dir(builtins))


def unbound(src):
    try:
        t = ast.parse(src)
    except SyntaxError:
        return None
    bound = set()
    for n in ast.walk(t):
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            bound.add(n.id)
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(n.name)
        elif isinstance(n, ast.arg):
            bound.add(n.arg)
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            bound.update((a.asname or a.name).split(".")[0] for a in n.names)
        elif isinstance(n, ast.ExceptHandler) and n.name:
            bound.add(n.name)
    return {n.id for n in ast.walk(t) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)} - bound - BI


ARMS = [("TEMPA_L (language)", REPO / "results", "tempa_l"), ("TEMPA_LF (language)", REPO / "results", "tempa_lf"),
        ("PyDex", REPO / "results", "pydex"), ("LLM_Direct", REPO / "results", "direct_llm"),
        ("Refactory", REPO / "results", "refactory"), ("TEMPA_L (Python rules)", HERE / "run/r0", "tempa_l")]
out = []
for name, root, arm in ARMS:
    c, ex = Counter(), []
    for pid in ORDER:
        f = root / pid / f"{arm}.csv"
        if not f.exists():
            continue
        for r in csv.DictReader(f.open()):
            if r["Fixed"] != "True" or not r["Patch"]:
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            new = (unbound(r["Patch"]) or set()) - (unbound(b) or set())
            c[r["Model"], "repairs"] += 1
            if new:
                c[r["Model"], "latent"] += 1
                c[r["Model"], "latent " + r["Source"]] += 1
                if len(ex) < 2:
                    ex.append((pid, r["Buggy"], sorted(new)))
    out.append(f"{name}: {sorted(c.items())} {ex}")
print("\n".join(out)); (HERE / "latent.txt").write_text("\n".join(out) + "\n")
