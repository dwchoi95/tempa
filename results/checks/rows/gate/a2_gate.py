"""A2: gate sweep. TEMPA_LF recomposed as compose.compose() / ablation._compose()
compose it, with RPS_GATE in GATES, for the full tool (tempa_l.csv) and the tool
without the builder's rules (tempa_l_fw.csv), escalated answers from LLM_Direct's
log (direct_llm.csv). Held-out: every distinct patch judged once on
augment._suite(pid) (R1-R5), cached by sha1 in cache/held_<pid>.json; on C1-C6
the acceptance suite is the official tests, so held = fixed (as ablation.py).
No LLM call.   python3 a2_gate.py
"""
import hashlib, json, os, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd
from scipy.stats import binomtest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import IDS, ORDER  # noqa
from src.experiments.ablation import _build_usd, _log  # noqa

HERE = ROOT / "results/checks/rows/gate"
GATES = (0.25, 0.5, 1.0)
TAUS = (0.1, 0.25, 0.5)
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
CS1 = ORDER[:5]
ARMS = {"full": "tempa_l", "-rules": "tempa_l_fw"}


def h(p):
    return hashlib.sha1(p.encode()).hexdigest()


def held_verdicts(pid, patches):
    """sha1(patch) -> passes T + held-out suite; cached, resumable."""
    f = HERE / "cache" / f"held_{pid}.json"
    have = json.loads(f.read_text()) if f.exists() else {}
    todo = {h(p): p for p in patches if h(p) not in have}
    if todo:
        from src.experiments.augment import _suite
        from src.runner.testing import run_tests
        suite = _suite(pid)
        with ThreadPoolExecutor(8) as ex:
            got = ex.map(lambda p: run_tests(p, suite).all_pass, todo.values())
            have.update(zip(todo, got))
        f.write_text(json.dumps(have))
    return have


def compose(local, direct, gate):
    """ablation._compose with the gate as a parameter."""
    out = {}
    for k, lo in local.items():
        if lo["fixed"] and lo["rps"] <= gate:
            out[k] = dict(lo, usd=0.0, esc=False)
            continue
        fb = direct[k]
        pick = lo if lo["fixed"] else None
        if fb["fixed"] and (pick is None or fb["rps"] < pick["rps"]):
            pick = dict(fb, source="llm")
        out[k] = dict(pick or {"fixed": False, "patch": "", "rps": None,
                               "source": "none", "rules": "[]"}, usd=fb["usd"], esc=True)
    return out


def rows():
    out = []
    for pid in ORDER:
        direct = _log(pid, "direct_llm")
        locs = {a: _log(pid, s) for a, s in ARMS.items()}
        if pid in CS1:
            pats = {v["patch"] for d in (direct, *locs.values()) for v in d.values() if v["fixed"]}
            ver = held_verdicts(pid, pats)
        for arm, loc in locs.items():
            for g in GATES:
                for (m, b), v in compose(loc, direct, g).items():
                    held = (ver[h(v["patch"])] if pid in CS1 else True) if v["fixed"] else False
                    out.append({"pid": pid, "id": IDS[pid], "model": m, "arm": arm, "gate": g,
                                "buggy": b, "fixed": v["fixed"], "held": held, "rps": v["rps"],
                                "source": v["source"], "esc": v["esc"], "usd": v["usd"],
                                "patch_sha": h(v["patch"]) if v["fixed"] else ""})
        print(IDS[pid], "composed", flush=True)
    return pd.DataFrame(out)


def summarize(d, scope):
    res = []
    for (m, arm, g), x in d.groupby(["model", "arm", "gate"], sort=False):
        ok = x[x.fixed]
        build = sum(_build_usd(p, m, "full" if arm == "full" else "-rules") for p in x.pid.unique())
        r = {"scope": scope, "model": m, "arm": arm, "gate": g, "n": len(x),
             "RR": 100 * x.fixed.mean(), "RR_held": 100 * x.held.mean(),
             **{f"RR_{t}": 100 * (x.held & (x.rps.astype(float) <= t)).mean() for t in TAUS},
             "RPS": ok.rps.astype(float).mean(), "esc": int(x.esc.sum()),
             "llm_kept": int((x.source == "llm").sum()),
             "C_api": x.usd.sum(), "C_build": build}
        r["C_tot"] = r["C_api"] + r["C_build"]
        res.append(r)
    return res


def mcnemar(d, scope):
    res = []
    for (m, g), x in d.groupby(["model", "gate"], sort=False):
        f = x[x.arm == "full"].set_index(["pid", "buggy"])
        w = x[x.arm == "-rules"].set_index(["pid", "buggy"]).reindex(f.index)
        for name, a, b in (("RR", f.fixed, w.fixed), ("RR_held", f.held, w.held),
                           ("RR_0.25", f.held & (f.rps.astype(float) <= .25),
                            w.held & (w.rps.astype(float) <= .25)),
                           ("no_esc", ~f.esc, ~w.esc)):
            b1, c1 = int((a & ~b).sum()), int((~a & b).sum())
            p = binomtest(min(b1, c1), b1 + c1).pvalue if b1 + c1 else 1.0
            res.append({"scope": scope, "model": m, "gate": g, "metric": name,
                        "full_only": b1, "rules_off_only": c1, "p_exact": p})
    return res


def main():
    f = HERE / "A2_rows.csv"
    d = pd.read_csv(f, keep_default_na=False) if f.exists() else rows()
    if not f.exists():
        d.to_csv(f, index=False)
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    d["buggy"] = d.buggy.astype(str)
    for c in ("fixed", "held", "esc"):
        d[c] = d[c].astype(str) == "True"
    s, mc = [], []
    for scope, x in (("all11", d), ("R1-R5", d[d.pid.isin(CS1)]), ("C1-C6", d[~d.pid.isin(CS1)])):
        s += summarize(x, scope)
        mc += mcnemar(x, scope)
    s, mc = pd.DataFrame(s), pd.DataFrame(mc)
    s.to_csv(HERE / "A2_gate.csv", index=False)
    mc.to_csv(HERE / "A2_mcnemar.csv", index=False)
    with pd.option_context("display.width", 250, "display.max_columns", 30):
        print(s.round(3).to_string(index=False))
        print(mc.to_string(index=False))
    # reproduction check against results/ablation.csv (gate 1.0)
    ab = pd.read_csv(ROOT / "results/ablation.csv")
    for arm in ARMS:
        a = ab[ab.arm == arm].assign(buggy=lambda z: z.buggy.astype(str)).set_index(["pid", "model", "buggy"])
        me = d[(d.arm == arm) & (d.gate == 1.0)].set_index(["pid", "model", "buggy"]).reindex(a.index)
        print(f"check {arm} gate 1.0 vs ablation.csv: fixed {(me.fixed == a.fixed).mean():.4f} "
              f"held {(me.held == a.heldout).mean():.4f} usd {((me.usd - a.api_usd).abs() < 1e-9).mean():.4f}")


if __name__ == "__main__":
    main()
