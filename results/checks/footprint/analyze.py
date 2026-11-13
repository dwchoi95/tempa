"""Footprint theorem on every repair: outside the footprint, does each repair behave
as its buggy program does, and how much of the input space does the footprint leave
untouched?  python3 -I analyze.py REPO  (after run.py; without its cache/, runs it first)   -> summary.csv"""
import csv, hashlib, json, statistics as st, sys
from collections import defaultdict
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core.footprint import footprint_lines  # noqa: E402
HERE = Path(__file__).resolve().parent
GROUPS = {("tempa_l", "rules"): "rules", ("tempa_l", "reference"): "transplant", ("tempa_lf", "llm"): "fallback",
          ("refactory", "reference"): "Refactory", ("pydex", "llm"): "PyDex", ("direct_llm", "llm"): "LLM_Direct"}


def sha(s):
    return hashlib.sha1(s.encode()).hexdigest()[:16]


if not any((HERE / "cache").glob("*.jsonl")):   # run.py's executions (1.4 GB, not tracked): make them first
    import subprocess; subprocess.run([sys.executable, "-I", str(HERE / "run.py"), str(REPO)], check=True)
runs = {}
for f in sorted((HERE / "cache").glob("*.jsonl")):
    for l in f.open():
        d = json.loads(l)
        runs[(f.stem, d["sha"])] = d.get("runs")

agg = defaultdict(lambda: defaultdict(list))
viol = []
for pdir in sorted((REPO / "results").glob("*/tempa_l.csv")):
    pid = pdir.parent.name
    for (arm, src), g in GROUPS.items():
        f = REPO / "results" / pid / f"{arm}.csv"
        if not f.exists():
            continue
        for r in csv.DictReader(f.open()):
            if r["Fixed"] != "True" or r["Source"] != src or not r["Patch"]:
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            rb, rc = runs.get((pid, sha(b))), runs.get((pid, sha(r["Patch"])))
            a = agg[(g, r["Model"])]
            if not rb or not rc or len(rb) != len(rc):
                a["missing"].append(1)
                continue
            try:
                F = footprint_lines(b, r["Patch"])
            except SyntaxError:
                a["unparsable"].append(1)
                continue
            out = [x for x in range(len(rb)) if F is not None and not (set(rb[x]["L"]) & F)]
            fin = [x for x in out if '"t": 1' not in rb[x]["o"] and '"t": 1' not in rc[x]["o"]]
            bad = [x for x in fin if rb[x]["o"] != rc[x]["o"]]
            right = [x for x in range(len(rb)) if rb[x]["ok"]]
            a["whole"].append(F is None)
            a["outside"].append(len(out) / len(rb))
            a["right_kept"].append(sum(1 for x in right if x in set(out)) / len(right) if right else None)
            a["checked"].append(len(fin)); a["timeout_skipped"].append(len(out) - len(fin)); a["bad"].append(len(bad))
            a["lines"].append(len(F) if F is not None else None)
            if bad:
                viol.append((g, r["Model"], pid, r["Buggy"], [(rb[x]["o"][:120], rc[x]["o"][:120]) for x in bad[:2]]))

rows = []
for (g, m), a in sorted(agg.items()):
    n = len(a["outside"])
    rk = [x for x in a["right_kept"] if x is not None]
    rows.append({"group": g, "model": m, "repairs": n, "missing": len(a["missing"]),
                 "whole_program": sum(a["whole"]), "mean_outside": round(st.mean(a["outside"]), 4) if n else None,
                 "mean_right_outside": round(st.mean(rk), 4) if rk else None,
                 "inputs_checked": sum(a["checked"]), "timeouts_skipped": sum(a["timeout_skipped"]),
                 "violations": sum(a["bad"]), "repairs_with_violation": sum(1 for x in a["bad"] if x)})
with (HERE / "summary.csv").open("w") as fh:
    w = csv.DictWriter(fh, rows[0].keys()); w.writeheader(); w.writerows(rows)
for x in rows:
    print(x)
print("violations:", len(viol))
for v in viol[:15]:
    print(v)
