"""`run.py search-size` — the candidates TEMPA_L validates per program.

Proposition 15 bounds the chance of accepting an overfitted patch by
|C(b)| (1 - eps)^n, where C(b), the candidates the tool would validate if none
passed, has at most eta_search + 2 eta_cand = 1,600 members; how many it
actually validates before one passes is measured here. This re-runs the frozen tool exactly as compare.py runs
TEMPA_L (T+ on R1-R5, the whole class as the pool) and logs, per program, how
many candidates the rule search and the transplant validated, whether the node
budget rather than exhaustion ended the rule search, and whether the patch is the
one logged in results/<pid>/tempa_l.csv.

    python run.py search-size --problem P   # -> results/search_size/<pid>.csv
    python run.py search-size --report      # determinism and the distribution
"""
from __future__ import annotations

import argparse
from pathlib import Path

import pandas as pd

from src.core.reference_repair import ReferenceIndex, local_repair
from src.core.repair import SearchBudget
from src.core.synthesis import load_fixer
from src.experiments._common import IDS, ORDER, load_pool, load_problem, tool_path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "results" / "search_size"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def run(pid: str) -> None:
    correct = load_pool(pid, "correct")
    index, budget = ReferenceIndex(correct), SearchBudget()
    files = sorted((ROOT / "benchmark" / pid / "buggy").glob("*.py"))
    rows = []
    for m in MODELS:
        prob = load_problem(pid, amplified=m)
        rules = load_fixer(tool_path(pid, m))
        log = pd.read_csv(ROOT / "results" / pid / "tempa_l.csv", keep_default_na=False)
        logged = dict(zip(log[log.Model == m].Buggy.astype(str), log[log.Model == m].Patch))
        for f in files:
            src = f.read_text()
            r = local_repair(src, prob, rules, index, budget)
            rows.append({"pid": pid, "model": m, "buggy": f.stem, "fixed": r.repaired,
                         "source": r.source, "depth": len(r.rules), "tried": r.tried,
                         "cut": r.cut, "same": (r.patch or "") == logged.get(f.stem, "")})
        print(f"{IDS[pid]} [{m}] done", flush=True)
    OUT.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(rows).to_csv(OUT / f"{pid}.csv", index=False)


def report() -> pd.DataFrame:
    d = pd.concat(pd.read_csv(f) for f in sorted(OUT.glob("*.csv")))
    print(f"{len(d)} runs; patch as logged {100 * d.same.mean():.2f}%; "
          f"rule search ended by the node budget {100 * d.cut.mean():.2f}% "
          f"({100 * d[d.fixed].cut.mean():.2f}% of repairs)")
    g = d[d.fixed].groupby("source").tried.describe(percentiles=[.5, .9, .99])
    print(g.round(1))
    return d


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py search-size")
    ap.add_argument("--problem", choices=ORDER)
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args(argv)
    if args.report:
        report()
    else:
        run(args.problem)
    return 0
