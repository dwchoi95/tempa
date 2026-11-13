"""Summarize the pruning A/B (run.py): per builder, the rule search with and without
footprint pruning; also checks the unpruned arm against the stored TEMPA_L results.
    python3 results/checks/prune/analyze.py   -> summary.csv"""
import csv, glob
from collections import defaultdict
from pathlib import Path
csv.field_size_limit(10**9)
ROOT = Path(__file__).resolve().parents[3]; HERE = Path(__file__).parent
T = lambda v: v == "True"
rows = [r for f in sorted(glob.glob(str(HERE / "rows/*.csv"))) for r in csv.DictReader(open(f))]
stored = {}
for f in glob.glob(str(ROOT / "results/*/tempa_l.csv")):
    for r in csv.DictReader(open(f)):
        stored[(Path(f).parent.name, r["Model"], r["Buggy"])] = r
out = []
for m in sorted({r["model"] for r in rows}):
    g = [r for r in rows if r["model"] == m]
    s = defaultdict(float)
    for r in g:
        st = stored[(r["pid"], m, r["buggy"])]
        s["programs"] += 1
        s["off_repaired"] += T(r["off_repaired"]); s["on_repaired"] += T(r["on_repaired"])
        s["only_on"] += T(r["on_repaired"]) and not T(r["off_repaired"])
        s["only_off"] += T(r["off_repaired"]) and not T(r["on_repaired"])
        s["same_patch"] += T(r["off_repaired"]) and r["off_patch"] == r["on_patch"]
        s["matches_stored"] += (T(r["off_repaired"]) == (st["Source"] == "rules")
                                and (not T(r["off_repaired"]) or r["off_patch"] == st["Patch"]))
        s["on_cut"] += T(r["on_cut"]); s["off_cut"] += T(r["off_cut"])
        if r["on_cut"] == "timeout":               # stopped at run.py's LIMIT: no counts
            s["on_timeout"] += 1
            continue
        s["off_tried"] += int(r["off_tried"]); s["on_tried"] += int(r["on_tried"]); s["on_pruned"] += int(r["on_pruned"])
        both = T(r["off_repaired"]) and T(r["on_repaired"])
        s["both_off_tried"] += both * int(r["off_tried"]); s["both_on_tried"] += both * int(r["on_tried"])
        s["off_seconds"] += float(r["off_seconds"]); s["on_seconds"] += float(r["on_seconds"])
    s = {k: int(v) if k != "off_seconds" and k != "on_seconds" else round(v, 1) for k, v in s.items()}
    s["validations_saved_%"] = round(100 * (1 - s["on_tried"] / s["off_tried"]), 1)
    s["saved_on_repaired_%"] = round(100 * (1 - s["both_on_tried"] / max(1, s["both_off_tried"])), 1)
    out.append({"model": m, **s})
    print(out[-1])
if out:
    with open(HERE / "summary.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, out[0].keys()); w.writeheader(); w.writerows(out)
