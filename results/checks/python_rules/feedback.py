"""What the static semantics' reasons do in the build loop, from the rule files of each round
(tools_lang/**/round*.rules): rules rejected in a round, and those whose name compiles in the
next round. No model call.
    python3 -I feedback.py REPO   -> feedback.txt"""
import re, sys
from collections import Counter
from pathlib import Path
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core.rulelang import compile_rules        # noqa: E402
HERE = Path(__file__).resolve().parent
name = re.compile(r"^(?:rule\s+)?(\S+?)[:\s]")
tot = Counter()
for d in sorted({f.parent for f in (REPO / "tools_lang").glob("**/round1.rules")}):
    m = d.name
    rounds = sorted(d.glob("round*.rules"), key=lambda f: int(f.stem[5:]))
    prev_bad = None
    for f in rounds:
        rules, errors = compile_rules(f.read_text())
        ok = {r.name for r in rules}
        bad = set()
        for e in errors:
            g = name.match(e)
            bad.add(g.group(1) if g else e)
        tot[m, "rules written"] += len(ok) + len(bad)
        tot[m, "rejected"] += len(bad)
        if prev_bad is not None:
            tot[m, "rejected then resubmitted"] += len(prev_bad)
            tot[m, "compiled next round"] += len(prev_bad & ok)
        prev_bad = bad
out = [f"{k[0]} {k[1]}: {v}" for k, v in sorted(tot.items())]
print("\n".join(out)); (HERE / "feedback.txt").write_text("\n".join(out) + "\n")
