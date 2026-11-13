"""Analysis 4: RR_tau with equal oracles, PyDex accepting T+ against TEMPA_LF, R1-R5. No LLM call.

  cs: results/pydex_oracle/hybrid_claude-sonnet-5.csv, arm PyDex+T+ (Section 5.6): all 1,783
      R1-R5 programs; the 72 whose original pick passes T but fails T+ were re-queried (ten fresh
      candidates, kept the closest passing T+), every other program keeps its original outcome,
      which accepting T+ cannot change (its pick passes T+, or no candidate passed T).
  gm: results/pydex_oracle/pairs_gpt-5.4-mini.csv, arm PyDex-10 accepting T+: all 1,783 R1-R5
      programs, each re-queried for ten fresh candidates (the same candidates read with T give
      PyDex-10 accepting T).
  TEMPA_LF: A1_rows.csv (= results/ablation.csv "full", Table 3's row), R1-R5 rows.
held = passes T + the held-out suite (augment._suite); RR_tau = held and RPS <= tau.
Exact McNemar per builder on the same programs.   python3 .../a4_equal_oracle.py
"""
import json, os, sys
from pathlib import Path

import pandas as pd
from scipy.stats import binomtest, wilcoxon

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import ORDER  # noqa
from src.experiments.ablation import _build_usd  # noqa

HERE = ROOT / "results/checks/rows/oos"
CS1 = ORDER[:5]
TAUS = (0.1, 0.25, 0.5)


def b(x):
    return x.astype(str) == "True"


def load():
    a = pd.read_csv(HERE / "A1_rows.csv", keep_default_na=False)
    a = a[a.pid.isin(CS1)].copy()
    a["rps"] = pd.to_numeric(a.rps, errors="coerce")
    a["fixed"], a["held"] = b(a.fixed), b(a.held)
    a["usd"] = a.api_usd.astype(float)
    hy = pd.read_csv(ROOT / "results/pydex_oracle/hybrid_claude-sonnet-5.csv")
    pk = pd.read_csv(ROOT / "results/pydex_oracle/pairs_gpt-5.4-mini.csv")
    arms = {
        ("claude-sonnet-5", "TEMPA_LF"): a[(a.model == "claude-sonnet-5") & (a.arm == "TEMPA_LF")],
        ("claude-sonnet-5", "PyDex (T, Table 3)"): a[(a.model == "claude-sonnet-5") & (a.arm == "PyDex")],
        ("claude-sonnet-5", "PyDex+T+ (hybrid)"): hy[hy.arm == "PyDex+T+"],
        ("gpt-5.4-mini", "TEMPA_LF"): a[(a.model == "gpt-5.4-mini") & (a.arm == "TEMPA_LF")],
        ("gpt-5.4-mini", "PyDex (T, Table 3)"): a[(a.model == "gpt-5.4-mini") & (a.arm == "PyDex")],
        ("gpt-5.4-mini", "PyDex-10 re-queried, T"): pk[(pk.arm == "PyDex-10") & (pk.accept == "T")],
        ("gpt-5.4-mini", "PyDex-10 re-queried, T+"): pk[(pk.arm == "PyDex-10") & (pk.accept == "T+")],
    }
    out = {}
    for k, x in arms.items():
        x = x.assign(buggy=x.buggy.astype(str)).set_index(["pid", "buggy"])
        assert len(x) == 1783, (k, len(x))
        out[k] = x[["fixed", "held", "rps", "usd"]]
    return out


def lf_cost(m):
    return sum(_build_usd(p, m, "full") for p in CS1)


def main():
    arms = load()
    rows, tests = [], []
    for (m, arm), x in arms.items():
        rows.append({"model": m, "arm": arm, "n": len(x), "RR": 100 * x.fixed.mean(), "RR_held": 100 * x.held.mean(),
                     **{f"RR_{t}": 100 * (x.held & (x.rps <= t)).mean() for t in TAUS},
                     "RPS": x.rps[x.fixed].mean(),
                     "C_tot": x.usd.sum() + (lf_cost(m) if arm == "TEMPA_LF" else 0.0)})
    for m in ("claude-sonnet-5", "gpt-5.4-mini"):
        lf = arms[(m, "TEMPA_LF")]
        for (mm, arm), y in arms.items():
            if mm != m or arm == "TEMPA_LF":
                continue
            y = y.reindex(lf.index)
            for met in ("RR_held", *[f"RR_{t}" for t in TAUS]):
                if met == "RR_held":
                    u, v = lf.held, y.held
                else:
                    t = float(met[3:]); u, v = lf.held & (lf.rps <= t), y.held & (y.rps <= t)
                b1, c1 = int((u & ~v).sum()), int((~u & v).sum())
                tests.append({"model": m, "vs": arm, "metric": met, "n": len(lf), "tempa_lf_pct": 100 * u.mean(),
                              "pydex_pct": 100 * v.mean(), "tempa_lf_only": b1, "pydex_only": c1,
                              "p_exact": binomtest(min(b1, c1), b1 + c1).pvalue if b1 + c1 else 1.0})
            both = lf.held & y.held
            tests.append({"model": m, "vs": arm, "metric": "RPS on both held (Wilcoxon)", "n": int(both.sum()),
                          "tempa_lf_pct": lf.rps[both].mean(), "pydex_pct": y.rps[both].mean(),
                          "tempa_lf_only": None, "pydex_only": None,
                          "p_exact": wilcoxon(lf.rps[both], y.rps[both]).pvalue})
    r, t = pd.DataFrame(rows), pd.DataFrame(tests)
    r.to_csv(HERE / "A4_metrics.csv", index=False)
    t.to_csv(HERE / "A4_mcnemar.csv", index=False)
    with pd.option_context("display.width", 250, "display.max_columns", 20):
        print(r.round(3).to_string(index=False))
        print(t.round(4).to_string(index=False))


if __name__ == "__main__":
    main()
