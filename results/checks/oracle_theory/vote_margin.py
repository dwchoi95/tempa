"""How far the class is from a wrong label. Every input each builder's generator drew for T_amp, kept or not, runs on the
41 voters of Definition 4.1, and the instructor's solution judges them: `worst` is the most voters sharing one wrong
output on an input, `dissent` the sampled voters wrong on some input.
    python3 -I vote_margin.py REPO   -> vote_margin.txt"""
import json, random, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.experiments.augment import (BENCH, CS1, MODELS, N_VOTERS, AGREE, _draw, _fresh, _outputs, held_keys,  # noqa: E402
                                     load_problem)
tot, lines = Counter(), []
for pid in CS1:
    problem = load_problem(pid, str(BENCH))
    reference = (BENCH / pid / "reference.py").read_text()
    pool = sorted((BENCH / pid / "correct").glob("*.py"))
    voters = [p.read_text() for p in random.Random(1).sample(pool, min(N_VOTERS, len(pool)))]
    for m in MODELS:
        code = (BENCH / pid / "amplified" / m / "generator.py").read_text()
        inputs, _ = _draw(code, f"{pid}:llm")
        cands = _fresh(inputs, held_keys(pid))
        ref = _outputs(reference, problem, cands)
        cands, ref = zip(*[(t, o) for t, o in zip(cands, ref) if o != "!err"])
        cands = list(cands)
        with ThreadPoolExecutor(10) as ex:
            votes = list(ex.map(lambda s: _outputs(s, problem, cands), voters))
        c = Counter(inputs=len(cands)); worst = worst_err = 0; bad = set()
        for i, y in enumerate(ref):
            v = Counter(x[i] for x in votes)
            n = len(voters) + 1
            top, k = (v + Counter({y: 1})).most_common(1)[0]
            c["labeled"] += top != "!err" and k / n >= AGREE
            c["label differs from the instructor"] += top != "!err" and k / n >= AGREE and top != y
            c["instructor outvoted"] += top != y
            wrong = {o: q for o, q in v.items() if o != y and o != "!err"}
            worst = max(worst, max(wrong.values(), default=0))
            worst_err = max(worst_err, v["!err"])
            bad |= {j for j, x in enumerate(votes) if x[i] != y}
        tot.update(c); tot["worst"] = max(tot["worst"], worst); tot["worst error block"] = max(tot["worst error block"], worst_err)
        tot["voter slots"] += len(voters); tot["dissenting voter slots"] += len(bad)
        kept = json.loads((BENCH / pid / "amplified" / m / "tests.json").read_text())
        lines.append(f"{pid} {m}: {dict(c)} worst {worst} of {len(voters) + 1}, errors {worst_err}, dissenting voters {len(bad)}, kept {len(kept)}")
        print(lines[-1], flush=True)
lines.append(f"total {dict(tot)}")
print(lines[-1]); (Path(__file__).resolve().parent / "vote_margin.txt").write_text("\n".join(lines) + "\n")
