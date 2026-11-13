"""Analysis 1: out-of-sample main results. No LLM call.

Per program and builder, every arm of Tables 2-3:
  from results/ablation.csv (Table 3's own rows, as vals/rrtau.py reads them):
      full (= TEMPA_LF), -rules, -amp, -rules-amp, line only, block only,
      cluster-once (= query per cluster), LLM_Direct, PyDex
  from rules_causality/A2_rows.csv: gate 0.25, with and without rules
  TEMPA_L: results/<pid>/tempa_l.csv
  Refactory: results/<pid>/refactory.csv, the authors' shipped run on R1-R5
      (Table 2 quotes their published aggregates, which have no per-program rows)
      and our run on C1-C6; repaired = passes T (results/checks/rows/refactory_oracle.csv
      on_T on R1-R5, as in "1,617 of Refactory's 1,620 repairs also pass T").
Held-out verdicts on R1-R5 for TEMPA_L and Refactory: T + augment._suite(pid), the
suite ablation.py and a2_gate.py use (Refactory's patch unwrapped, as augment.check
does), cached by sha1; on C1-C6 held = repaired (official tests), as ablation.py.
Subsets from worked_pairs.csv: worked / oos (never a worked pair, 1,446) /
oos_strict (also no text duplicate of a worked pair, 1,276) / all.

    python3 results/checks/rows/oos/a1_oos.py  -> A1_rows.csv, A1_metrics.csv, A1_mcnemar.csv
"""
import hashlib, json, os, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd
from scipy.stats import binomtest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import ORDER  # noqa
from src.experiments.ablation import _build_usd  # noqa

HERE = ROOT / "results/checks/rows/oos"
A2 = ROOT / "results/checks/rows/gate"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
CS1 = ORDER[:5]
TAUS = (0.1, 0.25, 0.5)
ARMS = ["TEMPA_LF", "TEMPA_L", "-rules", "-amp", "-rules-amp", "line only", "block only",
        "cluster-once", "gate 0.25", "gate 0.25 -rules", "LLM_Direct", "PyDex", "Refactory"]
AB = {"full": "TEMPA_LF"}           # ablation.csv arm -> name here


def sha(p):
    return hashlib.sha1(p.encode()).hexdigest()


def held(pid, patches, unwrap_=False):
    """sha1(patch) -> passes T + held-out suite. Reads a2_gate's cache, writes our own."""
    tag = "refactory_" if unwrap_ else ""
    mine = HERE / "cache" / f"held_{tag}{pid}.json"
    have = json.loads(mine.read_text()) if mine.exists() else {}
    if not unwrap_:
        have = {**json.loads((A2 / "cache" / f"held_{pid}.json").read_text()), **have}
    todo = {sha(p): p for p in patches if sha(p) not in have}
    if todo:
        from src.experiments.augment import _suite
        from src.experiments.refactory_results import unwrap
        from src.runner.testing import run_tests
        suite = _suite(pid)
        f = (lambda p: run_tests(unwrap(p), suite).all_pass) if unwrap_ else \
            (lambda p: run_tests(p, suite).all_pass)
        with ThreadPoolExecutor(8) as ex:
            got = dict(zip(todo, ex.map(f, todo.values())))
        have.update(got)
        old = json.loads(mine.read_text()) if mine.exists() else {}
        mine.write_text(json.dumps({**old, **got}))
        print(f"  judged {len(todo)} new patches on {pid}", flush=True)
    return have


def rows():
    ab = pd.read_csv(ROOT / "results/ablation.csv")
    ab = ab[~ab.arm.str.endswith("(run)")].copy()
    ab["arm"] = ab.arm.replace(AB)
    ab = ab.rename(columns={"heldout": "held"})[["arm", "pid", "model", "buggy", "fixed", "held", "rps", "api_usd"]]
    g = pd.read_csv(A2 / "A2_rows.csv", keep_default_na=False)
    g = g[g.gate.astype(float) == 0.25].copy()
    g["arm"] = g.arm.map({"full": "gate 0.25", "-rules": "gate 0.25 -rules"})
    g = g.rename(columns={"usd": "api_usd"})[ab.columns]
    for c in ("fixed", "held"):
        g[c] = g[c].astype(str) == "True"
    out = [ab, g]
    oracle = pd.read_csv(ROOT / "results/checks/rows/refactory_oracle.csv")
    oracle = oracle[oracle.arm == "refactory"].assign(buggy=lambda z: z.buggy.astype(str)).set_index(["pid", "buggy"])
    for pid in ORDER:
        l = pd.read_csv(ROOT / "results" / pid / "tempa_l.csv", keep_default_na=False)
        r = pd.read_csv(ROOT / "results" / pid / "refactory.csv", keep_default_na=False)
        for d in (l, r):
            d["fixed"] = d.Fixed.astype(str) == "True"
            d["Buggy"] = d.Buggy.astype(str)
        if pid in CS1:                       # Refactory repaired = its repair passes T
            r["fixed"] = r.fixed & pd.Series([bool(oracle.loc[(pid, b), "on_T"]) for b in r.Buggy], index=r.index)
            hl = held(pid, set(l.Patch[l.fixed]))
            hr = held(pid, set(r.Patch[r.fixed]), unwrap_=True)
        for arm, d, hv in (("TEMPA_L", l, hl if pid in CS1 else None), ("Refactory", r, hr if pid in CS1 else None)):
            hv_ = [(hv[sha(p)] if hv is not None else True) if ok else False for p, ok in zip(d.Patch, d.fixed)]
            x = pd.DataFrame({"arm": arm, "pid": pid, "model": d.Model.astype(str), "buggy": d.Buggy,
                              "fixed": d.fixed, "held": hv_,
                              "rps": pd.to_numeric(d.RPS, errors="coerce").where(d.fixed),
                              "api_usd": 0.0})
            if arm == "Refactory":           # builder-independent: one copy per builder
                x = pd.concat([x.assign(model=m) for m in MODELS])
            out.append(x)
    d = pd.concat(out, ignore_index=True)
    d["buggy"] = d.buggy.astype(str)
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    return d


SUBSETS = {"all": lambda d: d, "worked": lambda d: d[d.worked],
           "oos": lambda d: d[~d.worked], "oos_strict": lambda d: d[~d.worked & ~d.text_dup],
           "oos_same_edit": lambda d: d[~d.worked & d.same_edit],
           "oos_other_edit": lambda d: d[~d.worked & ~d.same_edit]}


def build_usd(arm, m):
    a = {"TEMPA_LF": "full", "TEMPA_L": "full", "gate 0.25": "full", "gate 0.25 -rules": "-rules"}.get(arm, arm)
    return 0.0 if arm in ("PyDex", "LLM_Direct", "Refactory") else sum(_build_usd(p, m, a) for p in ORDER)


def metrics(d):
    res = []
    for sub, f in SUBSETS.items():
        for (arm, m), x in f(d).groupby(["arm", "model"], sort=False):
            r = {"subset": sub, "arm": arm, "model": m, "n": len(x), "RR": 100 * x.fixed.mean(),
                 "RR_held": 100 * x.held.mean(),
                 **{f"RR_{t}": 100 * (x.held & (x.rps <= t)).mean() for t in TAUS},
                 "RPS": x.rps[x.fixed].mean(), "C_api": x.api_usd.sum(),
                 "C_build_full_set": build_usd(arm, m)}
            res.append(r)
    return pd.DataFrame(res)


def mcnemar(d):
    res = []
    for sub, f in SUBSETS.items():
        x = f(d)
        for m in MODELS:
            y = x[x.model == m]
            a = y[y.arm == "TEMPA_LF"].set_index(["pid", "buggy"])
            for other in ("PyDex", "LLM_Direct", "-rules", "cluster-once"):
                b = y[y.arm == other].set_index(["pid", "buggy"]).reindex(a.index)
                for met in ("RR", "RR_held", *[f"RR_{t}" for t in TAUS]):
                    if met == "RR":
                        u, v = a.fixed, b.fixed
                    elif met == "RR_held":
                        u, v = a.held, b.held
                    else:
                        t = float(met[3:])
                        u, v = a.held & (a.rps <= t), b.held & (b.rps <= t)
                    b1, c1 = int((u & ~v).sum()), int((~u & v).sum())
                    res.append({"subset": sub, "model": m, "vs": other, "metric": met, "n": len(a),
                                "tempa_lf_pct": 100 * u.mean(), "other_pct": 100 * v.mean(),
                                "tempa_lf_only": b1, "other_only": c1,
                                "p_exact": binomtest(min(b1, c1), b1 + c1).pvalue if b1 + c1 else 1.0})
    return pd.DataFrame(res)


def main():
    f = HERE / "A1_rows.csv"
    if f.exists():
        d = pd.read_csv(f, keep_default_na=False)
        d["rps"] = pd.to_numeric(d.rps, errors="coerce")
        for c in ("fixed", "held"):
            d[c] = d[c].astype(str) == "True"
        d["buggy"] = d.buggy.astype(str)
    else:
        d = rows()
    w = pd.read_csv(ROOT / "results/checks/baselines/worked_pairs.csv")
    w["buggy"] = w.buggy.astype(str)
    d = d[[c for c in d.columns if c not in ("worked", "text_dup", "same_edit")]].merge(
        w[["pid", "buggy", "worked", "text_dup", "same_edit"]], on=["pid", "buggy"], how="left", validate="m:1")
    assert d.worked.notna().all()
    d.to_csv(f, index=False)
    assert (d.groupby(["arm", "model"]).size() == 2970).all()
    s, mc = metrics(d), mcnemar(d)
    s.to_csv(HERE / "A1_metrics.csv", index=False)
    mc.to_csv(HERE / "A1_mcnemar.csv", index=False)
    with pd.option_context("display.width", 250, "display.max_columns", 30, "display.max_rows", 500):
        print(s.round(3).to_string(index=False))
        print(mc.round(4).to_string(index=False))


if __name__ == "__main__":
    main()
