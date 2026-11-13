"""Table 2's Median FL (Section 4.2): the median number of footprint lines over each tool's
repairs, all sources of a repair pooled. The footprint comes from the buggy program and its
repair alone (no execution, no cache). No model call.
    python3 -I results/checks/footprint/median_fl.py   -> median_fl.txt"""
import csv
import statistics as st
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.core.footprint import footprint_lines  # noqa: E402
from src.experiments._common import ORDER       # noqa: E402

csv.field_size_limit(10**9)
TOOLS = [("Refactory", "refactory", ("none",)), ("PyDex", "pydex", ("claude-sonnet-5", "gpt-5.4-mini")),
         ("TEMPA", "tempa_lf", ("claude-sonnet-5", "gpt-5.4-mini"))]


def main():
    out = []
    for name, arm, models in TOOLS:
        for m in models:
            sizes = []
            for pid in ORDER:
                for r in csv.DictReader((ROOT / "results" / pid / f"{arm}.csv").open()):
                    if r["Model"] != m or r["Fixed"] != "True" or not r["Patch"]:
                        continue
                    b = (ROOT / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
                    try:
                        f = footprint_lines(b, r["Patch"])
                    except SyntaxError:
                        continue
                    if f is not None:
                        sizes.append(len(f))
            out.append(f"{name:10s} {m:16s} repairs {len(sizes):5d}  median FL {st.median(sizes):g}")
    text = "\n".join(out) + "\n"
    (Path(__file__).parent / "median_fl.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
