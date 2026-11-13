"""Analysis 2: the rules' effect in each of the three builds (campaign r0, rebuilds r1, r2).
No LLM call.

with rules (TEMPA_LF): results/rebuild.csv (rebuild.report(): r0 = the campaign's TEMPA_LF,
    r1/r2 = each rebuild's frozen tool composed with LLM_Direct's logged answers judged
    against that rebuild's T+; held-out suite less that rebuild's T_amp inputs).
without rules: r0 = results/ablation.csv "-rules" (Table 3's row).
    r1/r2, C1-C6: the same rows (T+ = T; always-on rules, pool, data and Direct log are the
    campaign's, so nothing in this arm depends on the rebuild).
    r1/r2, R1-R5: TEMPA_L_fw re-run under the rebuild's T+ (a2_fw_jobs.py), composed exactly as
    rebuild.compose() composes TEMPA_LF (compose.compose, escalations answered by LLM_Direct's
    log judged against the rebuild's T+), and judged on the same suite as rebuild.report().
Exact McNemar per builder and build: with-only : without-only.
    python3 results/checks/rows/oos/a2_rebuild_rules.py
"""
import hashlib, json, os, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd
from scipy.stats import binomtest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import ORDER, load_problem  # noqa
from src.experiments.augment import _key, _suite, tplus_keys  # noqa
from src.experiments.compose import compose as compose_lf, escalated, judged_direct  # noqa
from src.experiments.results_io import read_events  # noqa
from src.runner.testing import run_tests  # noqa

HERE = ROOT / "results/checks/rows/oos"
BENCH, WORK, TOOLS = ROOT / "benchmark", ROOT / "rebuild_work", ROOT / "tools/rebuild"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
CS1 = ORDER[:5]
TAUS = (0.1, 0.25, 0.5)


def suite(r, pid, m):
    """rebuild.report()'s held-out suite for build r."""
    prob = load_problem(pid)
    amp = (WORK / f"r{r}") / pid / "amplified" / m / "tests.json"
    seen = tplus_keys(pid) | {_key(t) for t in json.loads(amp.read_text())}
    extra = _suite(pid)["tests"][len(prob["tests"]):]
    return dict(prob, tests=prob["tests"] + [t for t in extra if _key(t) not in seen])


def fw_rows(r, pid, m):
    """-rules under rebuild r on an R1-R5 assignment: compose + judge, cached."""
    f = HERE / "cache" / f"fw_r{r}_{pid}_{m}.csv"
    if f.exists():
        return pd.read_csv(f, keep_default_na=False)
    local = read_events(f"checks/rows/oos/rebuild_fw/r{r}/{m}", pid, "tempa_l_fw", m)
    assert len(local) == len(list((BENCH / pid / "buggy").glob("*.py"))), (r, pid, m, len(local))
    prob = load_problem(pid, str(WORK / f"r{r}"), m)
    need = escalated(local)
    direct = judged_direct(need, pid, m, prob, BENCH / pid / "buggy") + [x for x in local if x not in need]
    lf = compose_lf(local, direct)
    s = suite(r, pid, m)
    codes = {x["Patch"] for x in lf if x["Fixed"]}
    with ThreadPoolExecutor(8) as ex:
        held = dict(zip(codes, ex.map(lambda c: run_tests(c, s).all_pass, codes)))
    d = pd.DataFrame([{"buggy": str(x["Buggy"]), "fixed": bool(x["Fixed"]),
                       "held": bool(x["Fixed"]) and held[x["Patch"]],
                       "rps": x["RPS"] if x["Fixed"] else None, "api_usd": float(x["$API"] or 0),
                       "l_fixed": bool(next(y for y in local if y["Buggy"] == x["Buggy"])["Fixed"])}
                      for x in lf])
    d.to_csv(f, index=False)
    print(f"r{r} {pid} {m}: -rules composed and judged", flush=True)
    return d


def b(x):
    return x.astype(str) == "True"


def main():
    rb = pd.read_csv(ROOT / "results/rebuild.csv", keep_default_na=False)
    ab = pd.read_csv(ROOT / "results/ablation.csv", keep_default_na=False)
    for d in (rb, ab):
        d["buggy"] = d.buggy.astype(str)
        d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    rb["fixed"], rb["held"] = b(rb.fixed), b(rb.held)
    ab["fixed"], ab["held"] = b(ab.fixed), b(ab.heldout)
    ab["api_usd"] = ab.api_usd.astype(float)
    wo0 = ab[ab.arm == "-rules"]
    # check: rebuild.csv r0 is Table 3's TEMPA_LF
    full = ab[ab.arm == "full"].set_index(["pid", "model", "buggy"])
    r0 = rb[rb.rebuild == 0].set_index(["pid", "model", "buggy"]).reindex(full.index)
    print("r0 rebuild.csv vs ablation full: fixed", (r0.fixed == full.fixed).mean(), "held",
          (r0.held == full.held).mean(), "rps", ((r0.rps - full.rps).abs().fillna(0) < 1e-9).mean())
    rows, tests = [], []
    for r in (0, 1, 2):
        for m in MODELS:
            w = rb[(rb.rebuild == r) & (rb.model == m)].set_index(["pid", "buggy"])
            parts = []
            for pid in ORDER:
                if r > 0 and pid in CS1:
                    parts.append(fw_rows(r, pid, m).assign(pid=pid))
                else:
                    parts.append(wo0[(wo0.model == m) & (wo0.pid == pid)][["pid", "buggy", "fixed", "held", "rps", "api_usd"]])
            o = pd.concat(parts).assign(buggy=lambda z: z.buggy.astype(str)).set_index(["pid", "buggy"]).reindex(w.index)
            o["rps"] = pd.to_numeric(o.rps, errors="coerce")
            o["fixed"], o["held"] = o.fixed.astype(bool), o.held.astype(bool)
            assert o.fixed.notna().all() and len(o) == 2970
            gen = sum(json.loads(((BENCH if r == 0 else TOOLS / f"r{r}") / p / "amplified" / m / "cost.json").read_text())["usd"]
                      for p in CS1)
            build_w = w.reset_index().drop_duplicates("pid").build_usd.astype(float).sum()
            for arm, x, build in (("with rules", w, build_w), ("without rules", o, gen)):
                rows.append({"build": f"r{r}", "model": m, "arm": arm, "RR": 100 * x.fixed.mean(),
                             "RR_held": 100 * x.held.mean(),
                             **{f"RR_{t}": 100 * (x.held & (x.rps <= t)).mean() for t in TAUS},
                             "RPS": x.rps[x.fixed].mean(), "C_tot": x.api_usd.astype(float).sum() + build})
            for t in TAUS:
                u, v = w.held & (w.rps <= t), o.held & (o.rps <= t)
                b1, c1 = int((u & ~v).sum()), int((~u & v).sum())
                tests.append({"build": f"r{r}", "model": m, "tau": t, "with_pct": 100 * u.mean(), "without_pct": 100 * v.mean(),
                              "diff_pts": 100 * (u.mean() - v.mean()), "with_only": b1, "without_only": c1,
                              "p_exact": binomtest(min(b1, c1), b1 + c1).pvalue if b1 + c1 else 1.0})
    r_, t_ = pd.DataFrame(rows), pd.DataFrame(tests)
    r_.to_csv(HERE / "A2_metrics.csv", index=False)
    t_.to_csv(HERE / "A2_mcnemar.csv", index=False)
    rng = t_.groupby(["model", "tau"]).agg(with_min=("with_pct", "min"), with_max=("with_pct", "max"),
                                           without_min=("without_pct", "min"), without_max=("without_pct", "max"),
                                           diff_min=("diff_pts", "min"), diff_max=("diff_pts", "max"),
                                           p_max=("p_exact", "max")).reset_index()
    rng.to_csv(HERE / "A2_range.csv", index=False)
    with pd.option_context("display.width", 250, "display.max_columns", 30):
        print(r_.round(3).to_string(index=False))
        print(t_.round(4).to_string(index=False))
        print(rng.round(3).to_string(index=False))


if __name__ == "__main__":
    main()
