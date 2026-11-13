"""R1-R5 under one oracle each way: every arm's repairs judged by Refactory's own
harness (all of its tests, R2's 17 with global.py; printed values compared as
strings), Refactory's repairs judged by T, and the buggy programs themselves.
    PYTHONPATH=. python3 results/checks/rows/refactory_oracle.py [workers]
-> results/checks/rows/refactory_oracle.csv and a summary table."""
import pickle
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import pandas as pd

RF = Path("baselines/refactory").resolve()
ARMS = ["refactory", "pydex", "direct_llm", "tempa_l", "tempa_lf"]
CHUNK = 40


def judge(task):
    q, codes = task
    sys.path.insert(0, str(RF))
    import os
    os.chdir(RF)                      # basic_framework imports by relative path
    from basic_framework.core_testing import Tester
    t = Tester(str(RF / "data" / f"question_{q}"))
    out = {}
    for c in codes:
        try:
            tr = t.tv_code(c)
            out[c] = bool(tr) and all(tr.values())   # {} = the harness could not run it
        except Exception:
            out[c] = False
    return q, out


def main():
    from src.runner.testing import load_problem, run_tests
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rows, tasks = [], []
    for q in range(1, 6):
        pid = f"refactory_q{q}"
        bug = {f.stem: f.read_text() for f in Path(f"benchmark/{pid}/buggy").glob("*.py")}
        for arm in ARMS:
            d = pd.read_csv(f"results/{pid}/{arm}.csv", keep_default_na=False)
            for _, r in d.iterrows():
                ok = str(r.Fixed) == "True" and bool(r.Patch)
                rows.append(dict(pid=pid, q=q, arm=arm, model=r.Model, buggy=str(r.Buggy),
                                 fixed=ok, patch=r.Patch if ok else ""))
        for b, src in bug.items():
            rows.append(dict(pid=pid, q=q, arm="buggy", model="-", buggy=b, fixed=True, patch=src))
    d = pd.DataFrame(rows)
    for q, g in d[d.fixed].groupby("q"):
        codes = sorted(set(g.patch))
        tasks += [(q, codes[i:i + CHUNK]) for i in range(0, len(codes), CHUNK)]
    cache = Path("results/checks/rows/refactory_oracle.pkl")
    verdict = pickle.loads(cache.read_bytes()) if cache.exists() else {}
    tasks = [(q, [c for c in cs if (q, c) not in verdict]) for q, cs in tasks]
    with ProcessPoolExecutor(workers) as ex:
        for q, out in ex.map(judge, [t for t in tasks if t[1]]):
            verdict.update({(q, c): v for c, v in out.items()})
    cache.write_bytes(pickle.dumps(verdict))
    d["ref_oracle"] = [r.fixed and verdict[(r.q, r.patch)] for r in d.itertuples()]
    # Refactory's own repairs and the buggy programs, judged by T
    probs = {q: load_problem(f"refactory_q{q}") for q in range(1, 6)}
    sel = d.arm.isin(["refactory", "buggy"]) & d.fixed
    d["on_T"] = False
    d.loc[sel, "on_T"] = [run_tests(r.patch, probs[r.q]).all_pass for r in d[sel].itertuples()]
    d.drop(columns="patch").to_csv("results/checks/rows/refactory_oracle.csv", index=False)
    s = d.groupby(["arm", "model"]).agg(n=("buggy", "size"), fixed_T=("fixed", "sum"),
                                         ref_oracle=("ref_oracle", "sum"))
    s["rr_T"] = 100 * s.fixed_T / s.n
    s["rr_ref"] = 100 * s.ref_oracle / s.n
    print(s.round(2).to_string())
    print("Refactory's repairs passing T:", int(d[d.arm == "refactory"].on_T.fillna(False).sum()),
          "of", int(d[d.arm == "refactory"].fixed.sum()))
    print("buggy programs passing Refactory's harness:", int(d[d.arm == "buggy"].ref_oracle.sum()),
          "| passing T:", int(d[d.arm == "buggy"].on_T.sum()))
    print(d.groupby(["pid", "arm", "model"]).agg(n=("buggy", "size"), T=("fixed", "sum"),
                                                 ref=("ref_oracle", "sum")).to_string())


if __name__ == "__main__":
    main()
