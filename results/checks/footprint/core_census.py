"""What the footprint theorem excludes, counted on the buggy programs and on every repair, by source:
syntax outside the translation, inspection, __annotations__, finalizers, weak references, a yield a discarded
generator's handler would catch, open files, and modules that may be nondeterministic.   python3 -I core_census.py REPO   -> core_census.txt"""
import ast, csv, sys
from collections import Counter, defaultdict
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1])
ARMS = ("tempa_l", "tempa_lf", "refactory", "pydex", "direct_llm")
BAD = {"eval", "exec", "locals", "vars", "globals", "compile", "__import__", "breakpoint"}
MODS = {"random", "threading", "time", "datetime", "secrets", "uuid", "os", "weakref", "gc", "inspect", "ctypes", "signal", "multiprocessing", "asyncio", "concurrent", "subprocess"}

def marks(s):
    t, m = ast.parse(s), set()
    for n in ast.walk(t):
        if isinstance(n, (ast.With, ast.AsyncWith, ast.AsyncFor, ast.AsyncFunctionDef, ast.Await, ast.Match)):
            m.add(type(n).__name__)
        if isinstance(n, ast.Try) and n.finalbody:
            m.add("finally")
        if isinstance(n, (ast.Global, ast.Nonlocal, ast.Yield, ast.YieldFrom)):
            m.add("uses:" + type(n).__name__)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in BAD:
            m.add("call:" + n.func.id)
        if isinstance(n, ast.Attribute) and n.attr in ("_getframe", "f_locals", "f_globals", "__code__", "__dict__", "__del__"):
            m.add("attr:" + n.attr)
        if isinstance(n, ast.Name) and n.id == "__class__" or isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "super" and not n.args:
            m.add("uses:__class__")
        if isinstance(n, ast.Name) and n.id == "__annotations__" or isinstance(n, ast.Attribute) and n.attr == "__annotations__":
            m.add("uses:__annotations__")              # every module and class body sets it up in the translation
        if isinstance(n, ast.FunctionDef) and n.name == "__del__":
            m.add("def:__del__")
        if isinstance(n, ast.Try) and any(h.type is None or any(isinstance(x, ast.Name) and x.id in ("BaseException", "GeneratorExit")
                                                               for x in ast.walk(h.type)) for h in n.handlers) \
                and any(isinstance(x, (ast.Yield, ast.YieldFrom)) for b in n.body for x in ast.walk(b)):
            m.add("yield-in-exit-handler")             # a discarded generator would run the handler
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "open":
            m.add("call:open")                         # a file left open is flushed when it dies
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names:
                x = (getattr(n, "module", None) or a.name).split(".")[0]
                if x in MODS:
                    m.add("import:" + x)
    return m

seen, tally, where = {}, defaultdict(Counter), defaultdict(list)
for pid in sorted(p.parent.name for p in (REPO / "results").glob("*/tempa_l.csv")):
    for b in sorted((REPO / "benchmark" / pid / "buggy").glob("*.py")):
        tally["buggy"]["programs"] += 1
        for k in marks(b.read_text()):
            tally["buggy"][k] += 1
            where[k].append(f"{pid}/{b.stem}")
    for arm in ARMS:
        f = REPO / "results" / pid / f"{arm}.csv"
        if not f.exists():
            continue
        for r in csv.DictReader(f.open()):
            if r["Fixed"] != "True" or not r["Patch"]:
                continue
            g = f"{arm}/{r['Source']}"
            tally[g]["repairs"] += 1
            try:
                ms = marks(r["Patch"])
            except SyntaxError:
                tally[g]["unparsable"] += 1
                continue
            for k in ms:
                tally[g][k] += 1
                where[k].append(f"{pid}/{r['Buggy']}<{g}")
out = [f"{g}: {dict(sorted(c.items()))}" for g, c in sorted(tally.items())]
out += [f"{k}: {sorted(set(v))[:12]}" for k, v in sorted(where.items()) if len(set(v)) <= 40 or k.startswith("call")]
print("\n".join(out)); (Path(__file__).resolve().parent / "core_census.txt").write_text("\n".join(out) + "\n")
