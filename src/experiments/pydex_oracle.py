"""`run.py pydex-oracle` — PyDex given TEMPA's oracle, and PyDex's cost-quality
curve, on R1-R5, from one set of samples.

PyDex accepts against T; TEMPA accepts against T+. To separate what the oracle
buys from what the repairer does, PyDex is re-queried with its own prompt and
model, keeping all K = 10 candidates, and every candidate is judged once on T,
on T+ (the same builder's amplified suite TEMPA uses), and on the held-out suite.
Every variant below is then a different reading of the same samples:

    PyDex-k     (accept T | T+)  survivors among the first k candidates; the one
                                 closest to the student's program is kept (PyDex)
    PyDex-first (accept T | T+)  candidates in order until one passes; pays only
                                 for the calls made

    python run.py pydex-oracle query --problem P --model M   # costs; resumable
    python run.py pydex-oracle report --model M              # judges and tabulates

PyDex keeps the survivor closest to the student, so where its original pick
also passes T+, accepting against T+ keeps that very pick. Only programs whose
pick fails T+ can change, so PyDex+T+ is exact from re-querying those alone
(--failing-tplus) and keeping every other program's original outcome
(report --hybrid); this is how it is measured on claude-sonnet-5.

    results/pydex_oracle/<pid>/candidates_<model>.json
    results/pydex_oracle/report_<model>.csv
"""
from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd

from baselines.pydex.pydex import K_DEFAULT, ShotBank, repair, token_edit_distance
from src.experiments._common import IDS, ORDER, load_env, load_problem
from src.experiments.augment import _suite
from src.runner.testing import run_tests
from src.utils.metrics import rps

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "results" / "pydex_oracle"
CS1 = ORDER[:5]
KS = (1, 2, 5, 10)


def _cands(pid: str, model: str) -> Path:
    return OUT / pid / f"candidates_{model}.json"


def _failing_tplus(pid: str, model: str) -> set[str]:
    """Programs whose original PyDex pick passes T but fails T+."""
    d = pd.read_csv(ROOT / "results" / pid / "pydex.csv", keep_default_na=False)
    d = d[(d.Model == model) & (d.Fixed.astype(str) == "True")]
    tp = load_problem(pid, amplified=model)
    with ThreadPoolExecutor(16) as ex:
        ok = list(ex.map(lambda c: run_tests(c, tp).all_pass, d.Patch.astype(str)))
    return {str(b) for b, o in zip(d.Buggy, ok) if not o}


def query(pid: str, model: str, only: set[str] | None = None) -> None:
    """Sample K candidates per buggy program with PyDex's own prompt (on T)."""
    load_env()
    prob = load_problem(pid)                       # the prompt sees T, as PyDex does
    data = ROOT / "benchmark" / pid
    f = _cands(pid, model)
    f.parent.mkdir(parents=True, exist_ok=True)
    got = json.loads(f.read_text()) if f.exists() else {}
    bank = ShotBank(prob, data)
    todo = [b for b in sorted((data / "buggy").glob("*.py"))
            if b.stem not in got and (only is None or b.stem in only)]
    print(f"{IDS[pid]} [{model}]: {len(got)} on disk, {len(todo)} to query")
    for i, b in enumerate(todo):
        res = repair(b.read_text(), prob, model=model, k=K_DEFAULT, bank=bank)
        got[b.stem] = {"seconds": res.seconds, "candidates": res.candidates}
        if i % 25 == 0 or i == len(todo) - 1:      # resumable: a crash loses <25
            f.write_text(json.dumps(got))
    f.write_text(json.dumps(got))


def _judge(pid: str, model: str) -> dict:
    """Per distinct candidate: passes T, T+, held-out; once each."""
    suites = {"T": load_problem(pid), "T+": load_problem(pid, amplified=model),
              "H": _suite(pid)}
    got = json.loads(_cands(pid, model).read_text())
    codes = {c["code"] for v in got.values() for c in v["candidates"] if c["code"]}

    def verdict(code):
        return code, {k: run_tests(code, s).all_pass for k, s in suites.items()}

    with ThreadPoolExecutor(16) as ex:
        return dict(ex.map(verdict, codes))


def report(model: str) -> pd.DataFrame:
    rows = []
    for pid in CS1:
        got = json.loads(_cands(pid, model).read_text())
        v = _judge(pid, model)
        for stem, rec in got.items():
            src = (ROOT / "benchmark" / pid / "buggy" / f"{stem}.py").read_text()
            cs = rec["candidates"]
            for acc in ("T", "T+"):
                ok = [bool(c["code"]) and v[c["code"]][acc] for c in cs]
                for k in KS:
                    surv = [c["code"] for c, o in zip(cs[:k], ok[:k]) if o]
                    pick = min(surv, key=lambda c: token_edit_distance(src, c)) if surv else None
                    rows.append(_row(pid, stem, f"PyDex-{k}", acc, src, pick, v,
                                     sum(c["usd"] for c in cs[:k])))
                n = next((i + 1 for i, o in enumerate(ok) if o), len(cs))
                pick = cs[n - 1]["code"] if ok[n - 1] else None
                rows.append(_row(pid, stem, "PyDex-first", acc, src, pick, v,
                                 sum(c["usd"] for c in cs[:n])))
    df = pd.DataFrame(rows)
    df.to_csv(OUT / f"pairs_{model}.csv", index=False)
    g = df.groupby(["arm", "accept"], sort=False)
    rep = pd.DataFrame({
        "RR": 100 * g.fixed.mean(), "RR_held": 100 * g.held.mean(),
        "RPS": g.rps.mean(), "RR_0.25": 100 * g.small.mean(), "usd": g.usd.sum()}).round(3)
    rep.to_csv(OUT / f"report_{model}.csv")
    with pd.option_context("display.width", 160):
        print(rep)
    return df


def report_hybrid(model: str, suite: str = "heldout") -> pd.DataFrame:
    """PyDex and PyDex+T+ on every R1-R5 program: re-queried programs read from
    their candidates, every other program from its original run; "held" is the
    verdict on T plus the held-out suite (or plus the <suite> suite)."""
    rows = []
    for pid in CS1:
        orig = pd.read_csv(ROOT / "results" / pid / "pydex.csv", keep_default_na=False)
        orig = orig[orig.Model == model].set_index("Buggy")
        got = json.loads(_cands(pid, model).read_text()) if _cands(pid, model).exists() else {}
        v = _judge(pid, model) if got else {}
        held = _suite(pid, suite)
        picks = {}
        for stem, r in orig.iterrows():
            src = (ROOT / "benchmark" / pid / "buggy" / f"{stem}.py").read_text()
            o = str(r.Patch) if str(r.Fixed) == "True" else None
            n = o
            if stem in got:
                surv = [c["code"] for c in got[stem]["candidates"] if c["code"] and v[c["code"]]["T+"]]
                n = min(surv, key=lambda c: token_edit_distance(src, c)) if surv else None
            picks[stem] = (src, o, n, float(r["$API"] or 0))
        codes = {c for _s, o, n, _u in picks.values() for c in (o, n) if c}
        with ThreadPoolExecutor(16) as ex:
            hv = dict(zip(codes, ex.map(lambda c: run_tests(c, held).all_pass, codes)))
        for stem, (src, o, n, usd) in picks.items():
            for arm, pick in (("PyDex", o), ("PyDex+T+", n)):
                r_ = rps(src, pick) if pick else None
                h = bool(pick) and hv[pick]
                rows.append({"pid": pid, "buggy": stem, "arm": arm, "fixed": pick is not None,
                             "held": h, "rps": r_, "small": h and r_ is not None and r_ <= 0.25,
                             "usd": usd, "requeried": stem in got})
    df = pd.DataFrame(rows)
    df.to_csv(OUT / f"hybrid_{model}{'' if suite == 'heldout' else '_' + suite}.csv", index=False)
    g = df.groupby("arm", sort=False)
    rep = pd.DataFrame({"RR": 100 * g.fixed.mean(), "RR_held": 100 * g.held.mean(),
                        "RPS": g.rps.mean(), "RR_0.25": 100 * g.small.mean(),
                        "usd": g.usd.sum()}).round(3)
    print(rep)
    print("re-queried programs:", int(df[df.arm == "PyDex"].requeried.sum()))
    return df


def _row(pid, stem, arm, acc, src, pick, v, usd):
    r = rps(src, pick) if pick else None
    held = bool(pick) and v[pick]["H"]
    return {"pid": pid, "buggy": stem, "arm": arm, "accept": acc,
            "fixed": pick is not None, "held": held, "rps": r,
            "small": held and r is not None and r <= 0.25, "usd": usd}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py pydex-oracle")
    ap.add_argument("action", choices=["query", "report"])
    ap.add_argument("--problem", choices=CS1)
    ap.add_argument("--model", default="gpt-5.4-mini")
    ap.add_argument("--failing-tplus", action="store_true",
                    help="query only programs whose original pick fails T+")
    ap.add_argument("--hybrid", action="store_true",
                    help="report PyDex+T+ from re-queried programs plus original outcomes")
    ap.add_argument("--suite", default="heldout",
                    help="--hybrid: the suite beside T (benchmark/<pid>/<suite>.json)")
    args = ap.parse_args(argv)
    if args.action == "query":
        only = _failing_tplus(args.problem, args.model) if args.failing_tplus else None
        query(args.problem, args.model, only)
    elif args.hybrid:
        report_hybrid(args.model, args.suite)
    else:
        report(args.model)
    return 0
