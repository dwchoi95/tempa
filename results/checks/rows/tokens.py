"""Section 4.3, "Model cost": the tokens each tool's model calls generate over the 11 assignments.
PyDex's are its repair-time output tokens; TEMPA's are those of its build, its amplification, and
its fallback, and the ratio is how many times fewer TEMPA generates. No model call.
    python3 -I results/checks/rows/tokens.py   -> tokens.txt"""
import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.experiments._common import ORDER  # noqa: E402

MODELS = ("claude-sonnet-5", "gpt-5.4-mini")


def main():
    out = []
    for m in MODELS:
        build = amp = fallback = pydex = 0
        for pid in ORDER:
            build += json.loads((ROOT / "tools" / pid / m / "cost.json").read_text())["out_tokens"]
            f = ROOT / "benchmark" / pid / "amplified" / m / "cost.json"   # R1-R5 only: C1-C6 keep T
            if f.exists():
                amp += json.loads(f.read_text())["out"]
            for r in csv.DictReader((ROOT / "results" / pid / "summary.csv").open()):
                if r["Model"] == m and r["Approach"] == "PyDex":
                    pydex += int(float(r["OuT"]))
                if r["Model"] == m and r["Approach"] == "TEMPA_LF":
                    fallback += int(float(r["OuT"]))
        tempa = build + amp + fallback
        out.append(f"{m}: PyDex {pydex:,} output tokens; TEMPA {tempa:,} (build {build:,}, amplification "
                   f"{amp:,}, fallback {fallback:,}); {pydex / tempa:.1f} times fewer")
    text = "\n".join(out) + "\n"
    (Path(__file__).parent / "tokens.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
