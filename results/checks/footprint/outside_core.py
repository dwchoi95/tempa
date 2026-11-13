"""The footprint check on the repairs outside PyCore: a buggy program or a repair with a class body
or a comprehension. From run.py's cache, as analyze.py (without cache/, runs run.py first); no execution.
    python3 -I outside_core.py REPO   -> outside_core.txt"""
import ast, csv, hashlib, sys
from collections import Counter
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core.footprint import footprint_lines  # noqa: E402
import json                                     # noqa: E402
HERE = Path(__file__).resolve().parent
GROUPS = {("tempa_l", "rules"), ("tempa_l", "reference"), ("tempa_lf", "llm"), ("refactory", "reference"),
          ("pydex", "llm"), ("direct_llm", "llm")}
EXT = (ast.ClassDef, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
sha = lambda s: hashlib.sha1(s.encode()).hexdigest()[:16]
outside = lambda s: any(isinstance(n, EXT) for n in ast.walk(ast.parse(s)))
if not any((HERE / "cache").glob("*.jsonl")):   # run.py's executions (1.4 GB, not tracked): make them first
    import subprocess; subprocess.run([sys.executable, "-I", str(HERE / "run.py"), str(REPO)], check=True)
runs = {}
for f in sorted((HERE / "cache").glob("*.jsonl")):
    for l in f.open():
        d = json.loads(l); runs[(f.stem, d["sha"])] = d.get("runs")
c = Counter(); programs = set(); buggy = set()
for pdir in sorted((REPO / "results").glob("*/tempa_l.csv")):
    pid = pdir.parent.name
    for b in (REPO / "benchmark" / pid / "buggy").glob("*.py"):
        try:
            c["buggy programs"] += 1
            if outside(b.read_text()):
                buggy.add((pid, b.stem))
        except SyntaxError:
            c["buggy programs unparsable"] += 1
    for arm, src in sorted(GROUPS):
        f = REPO / "results" / pid / f"{arm}.csv"
        if not f.exists():
            continue
        for r in csv.DictReader(f.open()):
            if r["Fixed"] != "True" or r["Source"] != src or not r["Patch"]:
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            rb, rc = runs.get((pid, sha(b))), runs.get((pid, sha(r["Patch"])))
            if not rb or not rc or len(rb) != len(rc):
                continue
            try:
                F = footprint_lines(b, r["Patch"])
                ext = outside(b) or outside(r["Patch"])
            except SyntaxError:
                continue
            key = "outside PyCore" if ext else "PyCore"
            c[key, "repairs"] += 1
            if ext:
                programs.add((pid, r["Buggy"]))
            out = [x for x in range(len(rb)) if F is not None and not (set(rb[x]["L"]) & F)]
            fin = [x for x in out if '"t": 1' not in rb[x]["o"] and '"t": 1' not in rc[x]["o"]]
            c[key, "inputs outside the footprint"] += len(fin)
            c[key, "violations"] += sum(rb[x]["o"] != rc[x]["o"] for x in fin)
            for x, y in zip(rb, rc):
                if '"t": 1' in x["o"] or '"t": 1' in y["o"] or x["o"] == y["o"]:
                    continue
                c[key, "inputs with a changed outcome"] += 1
                c[key, "changed outcome missing the hint"] += F is not None and not set(x["L"]) & F
out = [f"{k}: {v}" for k, v in sorted(c.items(), key=str)]
out.append(f"buggy programs with a class body or comprehension: {len(buggy)}; programs in a repair pair outside PyCore: {len(programs)}")
print("\n".join(out)); (HERE / "outside_core.txt").write_text("\n".join(out) + "\n")
