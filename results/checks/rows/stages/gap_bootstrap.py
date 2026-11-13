"""Paired bootstrap of the model gap in small repairs, TRL rules against Python rules (Section 4.4).

g = RR_0.25(claude-sonnet-5) - RR_0.25(gpt-5.4-mini) for the main build with the fallback:
TEMPA (stage_rows.csv) and TEMPA^Python (python_rows.csv). Delta = g_Python - g_TRL.
Resamples buggy programs with replacement within each assignment, the same programs for all
four runs, B = 10,000, seed 0, percentile 95% intervals. Logs only, no model call.
    python3 -I results/checks/rows/stages/gap_bootstrap.py"""
from pathlib import Path
import numpy as np
import pandas as pd

HERE = Path(__file__).parent
MODELS, B, TAU = ["claude-sonnet-5", "gpt-5.4-mini"], 10_000, 0.25
st = pd.read_csv(HERE / "stage_rows.csv", dtype={"buggy": str})
py = pd.read_csv(HERE / "python_rows.csv", dtype={"buggy": str})
d = pd.concat([st[st.arm == "TEMPA"].assign(lang="TRL"), py[py.arm == "Python"].assign(lang="Python")])
d["s"] = (d.fixed.astype(str) == "True") & (d.held.astype(str) == "True") & (pd.to_numeric(d.rps) <= TAU)
w = d.pivot_table(index=["pid", "buggy"], columns=["lang", "model"], values="s", aggfunc="first")
assert w.notna().all().all() and len(w) == 2970, "the four runs must cover the same 2,970 programs"
cols = [(l, m) for l in ("TRL", "Python") for m in MODELS]
x = w[cols].to_numpy(dtype=float)                          # programs x (TRL c, TRL g, Py c, Py g)

rng, tot = np.random.default_rng(0), np.zeros((B, 4))
for pid, idx in w.groupby(level="pid").indices.items():     # stratified: per-assignment counts fixed
    tot += x[idx][rng.integers(0, len(idx), size=(B, len(idx)))].sum(axis=1)
rr, rr0 = 100 * tot / len(x), 100 * x.mean(axis=0)
stats = {"g_TRL": (rr[:, 0] - rr[:, 1], rr0[0] - rr0[1]), "g_Python": (rr[:, 2] - rr[:, 3], rr0[2] - rr0[3])}
stats["Delta"] = (stats["g_Python"][0] - stats["g_TRL"][0], stats["g_Python"][1] - stats["g_TRL"][1])

out = [f"RR_0.25 (%, {len(x)} programs): " + ", ".join(f"{l} {m} {v:.1f}" for (l, m), v in zip(cols, rr0)),
       f"paired stratified bootstrap, B = {B}, seed 0, percentile 95%"]
for k, (bs, pt) in stats.items():
    lo, hi = np.percentile(bs, [2.5, 97.5])
    out.append(f"{k:9s} {pt:5.1f}  [{lo:5.1f}, {hi:5.1f}]  share of replicates <= 0: {(bs <= 0).mean():.4f}")
(HERE / "gap_bootstrap.txt").write_text("\n".join(out) + "\n")
print("\n".join(out))
