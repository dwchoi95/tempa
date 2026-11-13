"""Table 3 (Section 4.3): each tool's model cost and average time taken (ATT) over the 2,970
buggy programs. API cost and ATT pool results/<pid>/summary.csv over the 11 assignments
(ATT weighted by programs); PyDex's cost under prompt caching is its PyDex_PC row; TEMPA's
build cost includes amplification, as A1_metrics.csv gives it. No model call.
    python3 -I results/checks/rows/table3.py   -> table3.txt"""
import csv
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.experiments._common import ORDER  # noqa: E402

ROWS = [("Refactory", "Refactory", "none"),
        ("PyDex_claude", "PyDex", "claude-sonnet-5"), ("PyDex_gpt", "PyDex", "gpt-5.4-mini"),
        ("TEMPA_claude", "TEMPA_LF", "claude-sonnet-5"), ("TEMPA_gpt", "TEMPA_LF", "gpt-5.4-mini")]


def pooled():
    agg = {}
    for pid in ORDER:
        for r in csv.DictReader((ROOT / "results" / pid / "summary.csv").open()):
            a = agg.setdefault((r["Approach"], r["Model"]), [0.0, 0.0, 0.0])
            n = float(r["N"])
            a[0] += n; a[1] += float(r["ATT_all"]) * n; a[2] += float(r["$API"])
    return agg


def main():
    agg = pooled()
    build = {(r["arm"], r["model"]): float(r["C_build_full_set"] or 0)
             for r in csv.DictReader((Path(__file__).parent / "oos" / "A1_metrics.csv").open())
             if r["subset"] == "all"}
    out = [f"{'Tool':14s} {'$Build':>8s} {'$API':>8s} {'$Total':>8s} {'(cached)':>9s} {'ATT (s)':>8s}"]
    for name, arm, model in ROWS:
        n, att, api = agg[(arm, model)]
        b = build.get((arm, model), 0.0)
        cached = f"({agg[('PyDex_PC', model)][2]:.2f})" if arm == "PyDex" else ""
        out.append(f"{name:14s} {b:8.2f} {api:8.2f} {b + api:8.2f} {cached:>9s} {att / n:8.2f}")
    text = "\n".join(out) + "\n"
    (Path(__file__).parent / "table3.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
