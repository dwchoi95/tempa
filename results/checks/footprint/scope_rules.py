"""Section 4.2, "Expressiveness": in the main build's 22 tools, the rules the builders wrote,
those TRL's checks reject (and why), the rules that pass and change a scope, the rule repairs
that use them, and how many of those repairs have a footprint beyond the lines they edit.
No model call.
    python3 -I results/checks/footprint/scope_rules.py   -> scope_rules.txt"""
import csv
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.core import rulelang as L                       # noqa: E402
from src.core.footprint import footprint_lines           # noqa: E402
from src.experiments._common import ORDER, tool_path     # noqa: E402

csv.field_size_limit(10**9)
MODELS = ("claude-sonnet-5", "gpt-5.4-mini")


def main():
    c = Counter()
    reasons = Counter()
    for pid in ORDER:
        for m in MODELS:
            rules, errors = L.compile_rules((ROOT / tool_path(pid, m)).read_text())
            scope = {r.name for r in rules if L.effect(r) != (frozenset(), False)}
            c[(m, "pass")] += len(rules); c[(m, "rejected")] += len(errors); c[(m, "scope rules")] += len(scope)
            reasons.update("scope" if "scope" in str(e).lower() else "other" for e in errors)
            for r in csv.DictReader((ROOT / "results" / pid / "tempa_lf.csv").open()):
                if r["Model"] != m or r["Fixed"] != "True" or r["Source"] != "rules":
                    continue
                if not set(json.loads(r["Rules_L"] or "[]")) & scope:
                    continue
                c[(m, "scope-rule repairs")] += 1
                b = (ROOT / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
                f, sites = footprint_lines(b, r["Patch"]), footprint_lines(b, r["Patch"], sites_only=True)
                c[(m, "beyond the edited lines")] += f is None or f != sites
    out = []
    for m in MODELS:
        out.append(f"{m}: written {c[(m, 'pass')] + c[(m, 'rejected')]}, rejected {c[(m, 'rejected')]}, "
                   f"pass {c[(m, 'pass')]}, scope rules {c[(m, 'scope rules')]}, scope-rule repairs "
                   f"{c[(m, 'scope-rule repairs')]}, beyond the edited lines {c[(m, 'beyond the edited lines')]}")
    total = lambda k: sum(c[(m, k)] for m in MODELS)  # noqa: E731
    out.append(f"both: written {total('pass') + total('rejected')}, rejected {total('rejected')} "
               f"(for a scope: {reasons['scope']}), pass {total('pass')}, scope rules {total('scope rules')}")
    text = "\n".join(out) + "\n"
    (Path(__file__).parent / "scope_rules.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
