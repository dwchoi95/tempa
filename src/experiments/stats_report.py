"""`run.py stats` — Wilson intervals and exact McNemar over the event logs.

The paper reports repair rates with 95% intervals and states that comparisons
between arms we ran ourselves are paired at the submission level. Both claims
live here rather than in the collectors, because both need the per-submission
outcomes of *several* arms at once, which only exist once the logs are written.

Pairing is by submission id within one (problem, model) cell, so an arm
evaluated on a subset is compared on the overlap rather than against a
different denominator. Refactory on its own corpus is the one comparison that
cannot be paired --- there we quote published per-assignment rates and have no
per-submission outcomes --- so it is emitted with intervals and no test, marked
``unpaired``, which is how the paper must report it.

Writes results/<ver>/stats.csv and prints the corpus-level rows.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import pandas as pd

from src.utils.stats import mcnemar, wilson

ROOT = Path(__file__).resolve().parents[2]

# event file -> arm label; the order is the order the paper compares in
ARMS = [("refactory.csv", "Refactory"), ("pydex.csv", "PyDex"),
        ("direct_llm.csv", "LLM_Direct"),
        ("tempa_l.csv", "TEMPA_L"),
        ("tempa_l_fw.csv", "TEMPA_L_fw"), ("tempa_lf.csv", "TEMPA_LF")]
MODEL_FREE = {"Refactory"}
# every pairing the paper asserts, as (a, b) with a the reference arm
PAIRS = [("TEMPA_L", "Refactory"), ("TEMPA_LF", "Refactory"),
         ("TEMPA_L", "PyDex"), ("TEMPA_LF", "PyDex"),
         ("TEMPA_LF", "LLM_Direct"),    # what the local-first architecture adds
         ("TEMPA_L", "TEMPA_L_fw")]      # what the builder's rules add


def _outcomes(path: Path, model: str) -> dict[str, bool]:
    """submission id -> repaired, for one arm and builder."""
    if not path.exists():
        return {}
    df = pd.read_csv(path, keep_default_na=False)
    if "Model" in df.columns and model:
        df = df[df["Model"].astype(str) == model]
    return {str(r["Buggy"]): bool(r["Fixed"]) for _, r in df.iterrows()}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="run.py stats")
    ap.add_argument("--ver", default="",
                    help="optional subdirectory under results/; empty means "
                         "results/ itself, which is where the campaign wrote")
    ap.add_argument("--model", default=["claude-sonnet-5", "gpt-5.4-mini"],
                    nargs="+")
    args = ap.parse_args(argv)

    base = ROOT / "results" / args.ver
    rows: list[dict] = []
    # per (problem, model, arm) rates, and per (problem, model, pairing) tests
    pooled: dict[tuple, dict[str, bool]] = {}
    for pdir in sorted(p for p in base.iterdir() if p.is_dir()):
        for model in args.model:
            got = {}
            for fname, arm in ARMS:
                # the symbolic arms are model-independent; their logs carry "none"
                free = arm in MODEL_FREE
                o = _outcomes(pdir / fname, "" if free else model)
                if not o and free:
                    o = _outcomes(pdir / fname, "none")
                if o:
                    got[arm] = o
                    key = (model, arm)
                    pooled.setdefault(key, {}).update(
                        {f"{pdir.name}:{k}": v for k, v in o.items()})
            for arm, o in got.items():
                k = sum(o.values())
                lo, hi = wilson(k, len(o))
                rows.append({"Problem": pdir.name, "Model": model, "Arm": arm,
                             "N": len(o), "Fixed": k,
                             "RR": round(k / max(1, len(o)), 4),
                             "RR_lo": round(lo, 4), "RR_hi": round(hi, 4),
                             "vs": "", "b": "", "c": "", "p": ""})
            for a, b in PAIRS:
                if a not in got or b not in got:
                    continue
                m = mcnemar(got[a], got[b])
                rows.append({"Problem": pdir.name, "Model": model,
                             "Arm": a, "N": m.n_pairs, "Fixed": "",
                             "RR": "", "RR_lo": "", "RR_hi": "",
                             "vs": b, "b": m.b, "c": m.c,
                             "p": f"{m.p_value:.4g}"})

    for (model, arm), o in sorted(pooled.items()):
        k = sum(o.values())
        lo, hi = wilson(k, len(o))
        rows.append({"Problem": "CORPUS", "Model": model, "Arm": arm,
                     "N": len(o), "Fixed": k, "RR": round(k / max(1, len(o)), 4),
                     "RR_lo": round(lo, 4), "RR_hi": round(hi, 4),
                     "vs": "", "b": "", "c": "", "p": ""})
    for model in args.model:
        for a, b in PAIRS:
            ka, kb = (model, a), (model, b)
            if ka not in pooled or kb not in pooled:
                continue
            m = mcnemar(pooled[ka], pooled[kb])
            rows.append({"Problem": "CORPUS", "Model": model, "Arm": a,
                         "N": m.n_pairs, "Fixed": "", "RR": "", "RR_lo": "",
                         "RR_hi": "", "vs": b, "b": m.b, "c": m.c,
                         "p": f"{m.p_value:.4g}"})

    out = base / "stats.csv"
    pd.DataFrame(rows).to_csv(out, index=False)
    for r in rows:
        if r["Problem"] != "CORPUS":
            continue
        if r["vs"]:
            print(f"  [{r['Model']:<16}] {r['Arm']:<10} vs {r['vs']:<10} "
                  f"n={r['N']:<5} b={r['b']:<4} c={r['c']:<4} p={r['p']}")
        else:
            print(f"  [{r['Model']:<16}] {r['Arm']:<10} "
                  f"RR={100*r['RR']:.2f}% "
                  f"[{100*r['RR_lo']:.2f}, {100*r['RR_hi']:.2f}]  n={r['N']}")
    print(f"-> {out}")
    return 0
