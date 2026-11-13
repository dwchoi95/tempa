"""Section 4.5, "From written to used": per builder, over the main build's 11 tools, the rules it
wrote, those TRL's checks pass, and those TEMPA's repairs use (the builder's rules, read from the
Rules_L of results/<pid>/tempa_lf.csv). No model call.
    python3 -I results/checks/rows/rule_traits/rules_used.py   -> rules_used.txt"""
import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from src.core import rulelang as L                        # noqa: E402
from src.experiments._common import ORDER, tool_path      # noqa: E402

csv.field_size_limit(10**9)
MODELS = ("claude-sonnet-5", "gpt-5.4-mini")


def main():
    out = []
    for m in MODELS:
        written = passing = used = 0
        for pid in ORDER:
            rules, errors = L.compile_rules((ROOT / tool_path(pid, m)).read_text())
            names = {r.name for r in rules}
            written += len(rules) + len(errors)
            passing += len(names)
            seen = set()
            for r in csv.DictReader((ROOT / "results" / pid / "tempa_lf.csv").open()):
                if r["Model"] == m and r["Fixed"] == "True":
                    seen |= set(json.loads(r["Rules_L"] or "[]")) & names
            used += len(seen)
        out.append(f"{m}: written {written}, pass {passing}, used {used} "
                   f"({100 * used / passing:.0f}% of those passing)")
    text = "\n".join(out) + "\n"
    (Path(__file__).parent / "rules_used.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
