"""Rules, non-blank lines per rule, and build spend of each form over the three builds, per builder.
A Python tool's lines are its whole files, helpers included, over its rules; a rule file's are the
lines of the rules the static semantics accepts, over those rules.
    python3 -I rule_size.py REPO   -> rule_size.txt"""
import json, re, sys
from collections import Counter
from pathlib import Path
REPO = Path(sys.argv[1]); HERE = REPO / "results/checks/python_rules"
sys.path.insert(0, str(REPO))
from src.core.rulelang import compile_rules        # noqa: E402
M = ("claude-sonnet-5", "gpt-5.4-mini")
count = lambda t: sum(bool(l.strip()) for l in t.splitlines())
lines = lambda f: count(f.read_text()) if f.exists() else 0


def accepted_lines(f):
    """Non-blank lines of a rule file's accepted rules, and how many rules it holds."""
    blocks = [b for b in re.split(r"(?m)^(?=rule )", f.read_text()) if b.startswith("rule ")]
    names = {r.name for r in compile_rules(f.read_text())[0]}
    return sum(count(b) for b in blocks if b.split()[1] in names), len(blocks)


tot = Counter()
for b, p, m, r in json.loads((HERE / "audit.json").read_text()):
    lang = REPO / "tools_lang" / ("" if b == "r0" else f"rebuild/{b}") / p / m
    py = HERE / "tools_python" / b / p / m
    tot[m, "python", "rules"] += r["python"]["rules"]
    tot[m, "python", "written"] += r["python"]["rules"]
    tot[m, "python", "lines"] += lines(py / "fixer.py") + lines(py / "learned.py")
    n, written = accepted_lines(lang / "fixer.rules")
    tot[m, "language", "rules"] += r["language"]["rules"]
    tot[m, "language", "written"] += written
    tot[m, "language", "lines"] += n
    for form, d in (("language", lang), ("python", py)):
        tot[m, form, "usd"] += float(json.loads((d / "cost.json").read_text()).get("usd") or 0)
out = []
for m in M:
    for form in ("python", "language"):
        g = lambda k: tot[m, form, k]
        out.append(f"{m} {form}: rules {g('rules')} of {g('written')} lines {g('lines')} per rule {g('lines') / g('rules'):.1f} usd {g('usd'):.2f}")
print("\n".join(out)); (HERE / "rule_size.txt").write_text("\n".join(out) + "\n")
