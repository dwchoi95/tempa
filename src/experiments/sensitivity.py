"""`run.py sensitivity` — Proposition 15 measured: overfitting against n and |C(b)|.

Proposition 15 bounds the chance that the local strategies return a patch departing
from the class by |C(b)| (1 - eps)^n. So a repair accepted against more
amplified tests should hold more often, and a larger search should need more of
them. On R1-R5 the frozen tools ran without the fallback (TEMPA_L), accepting
against T plus the first n amplified tests, with the rule search capped at b
validated candidates:

    compare --no-llm --amplified --amp-n n --max-nodes b --ver sensitivity/n<n>_b<b>

n = 0 and n = 100 at b = 1,000 are TEMPA_L's own runs under T and under T+. A
repair overfits if it fails the held-out suite.

    python run.py sensitivity   # -> results/sensitivity.csv and the table
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd
from scipy.stats import binomtest

from src.experiments._common import ORDER
from src.experiments.augment import _suite
from src.runner.testing import run_tests

ROOT = Path(__file__).resolve().parents[2]
R = ROOT / "results"


def cells() -> dict[tuple[int, int], str]:
    """(n, b) -> the directory, under results/ and templated on {pid}, holding
    that run's tempa_l.csv."""
    out = {(0, 1000): "{pid}/no_amplification", (100, 1000): "{pid}"}
    for d in sorted((R / "sensitivity").glob("n*_b*")):
        n, b = d.name[1:].split("_b")
        out[(int(n), int(b))] = f"sensitivity/{d.name}/{{pid}}"
    return out


def judge() -> pd.DataFrame:
    rows = []
    for pid in ORDER[:5]:
        suite = _suite(pid)
        logs = {nb: pd.read_csv(R / sub.format(pid=pid) / "tempa_l.csv", keep_default_na=False)
                for nb, sub in cells().items()}
        patches = {p for d in logs.values() for p in d[d.Fixed.astype(str) == "True"].Patch}
        with ThreadPoolExecutor(16) as ex:
            held = dict(zip(patches, ex.map(lambda c: run_tests(c, suite).all_pass, patches)))
        for (n, b), d in logs.items():
            for (m, s), g in d[d.Fixed.astype(str) == "True"].groupby(["Model", "Source"]):
                rows.append({"n": n, "b": b, "model": m, "pid": pid, "source": s, "repaired": len(g),
                             "overfit": int(sum(not held[p] for p in g.Patch))})
    return pd.DataFrame(rows)


def main(argv=None) -> int:
    d = judge()
    d.to_csv(R / "sensitivity.csv", index=False)
    g = d.groupby(["model", "b", "n"])[["repaired", "overfit"]].sum().reset_index()
    ci = [binomtest(o, r).proportion_ci(method="wilson") if r else None
          for o, r in zip(g.overfit, g.repaired)]
    g["rate"] = 100 * g.overfit / g.repaired
    g["lo"] = [100 * c.low for c in ci]
    g["hi"] = [100 * c.high for c in ci]
    print(g.round(2).to_string(index=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
