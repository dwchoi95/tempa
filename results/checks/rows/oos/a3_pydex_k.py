"""PyDex-k for every k = 1..10 (and PyDex-first), accepting T or T+, on gpt-5.4-mini,
from the re-queried candidates in results/pydex_oracle/<pid>/candidates_gpt-5.4-mini.json.
Same reading as src/experiments/pydex_oracle.report() (which tabulated k in {1,2,5,10}
only): survivors among the first k candidates, the one closest to the student's program
kept; cost = the first k candidates' list-price usd. Candidates exist on R1-R5 only (the
original PyDex run on C1-C6 kept its pick alone), so this is R1-R5. Every distinct
candidate is judged once on T, T+ and T + held-out (pydex_oracle._judge), cached here.
No LLM call.   python3 results/checks/rows/oos/a3_pydex_k.py -> pydex_k_gm.csv
"""
import functools, json, os, sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from baselines.pydex.pydex import token_edit_distance  # noqa
from src.experiments import pydex_oracle as po  # noqa
from src.experiments._common import ORDER  # noqa

HERE = ROOT / "results/checks/rows/oos"
M = "gpt-5.4-mini"
po.rps = functools.lru_cache(maxsize=None)(po.rps)   # _row recomputes RPS for every reading


def verdicts(pid):
    f = HERE / "cache" / f"pydex_verdicts_{pid}_{M}.json"
    if not f.exists():
        f.write_text(json.dumps(po._judge(pid, M)))
        print(pid, "judged", flush=True)
    return json.loads(f.read_text())


def main():
    rows = []
    for pid in ORDER[:5]:
        got = json.loads(po._cands(pid, M).read_text())
        v = verdicts(pid)
        for stem, rec in got.items():
            src = (ROOT / "benchmark" / pid / "buggy" / f"{stem}.py").read_text()
            cs = rec["candidates"]
            dist = {}                          # token_edit_distance once per candidate, not per reading

            def key(c):
                if c not in dist:
                    dist[c] = token_edit_distance(src, c)
                return dist[c]
            for acc in ("T", "T+"):
                ok = [bool(c["code"]) and v[c["code"]][acc] for c in cs]
                for k in range(1, 11):
                    surv = [c["code"] for c, o in zip(cs[:k], ok[:k]) if o]
                    pick = min(surv, key=key) if surv else None
                    rows.append(po._row(pid, stem, f"PyDex-{k}", acc, src, pick, v, sum(c["usd"] for c in cs[:k])))
                n = next((i + 1 for i, o in enumerate(ok) if o), len(cs))
                rows.append(po._row(pid, stem, "PyDex-first", acc, src, cs[n - 1]["code"] if ok[n - 1] else None,
                                    v, sum(c["usd"] for c in cs[:n])))
    d = pd.DataFrame(rows)
    d.to_csv(HERE / "pydex_k_gm.csv", index=False)
    # check against the paper's own reading (k in {1, 2, 5, 10} and first)
    old = pd.read_csv(ROOT / "results/pydex_oracle/pairs_gpt-5.4-mini.csv")
    j = old.merge(d, on=["pid", "buggy", "arm", "accept"], suffixes=("_old", ""))
    print("rows checked", len(j), "of", len(old),
          {c: float(((j[c] == j[c + "_old"]) if j[c].dtype == bool else
                     (((j[c] - j[c + "_old"]).abs() < 1e-9) | (j[c].isna() & j[c + "_old"].isna()))).mean())
           for c in ("fixed", "held", "rps", "usd")})


if __name__ == "__main__":
    main()
