"""`run.py rebuild` — how far the results move when the builders run again.

The builders are sampled LLMs, so building an assignment again yields other
rules and another input generator. Rebuild r in {1, 2} synthesizes every tool
and every generator anew, from the same data with the same prompts and budgets
as the campaign (r = 0), and is evaluated as the campaign is: TEMPA_L by the
tool alone, TEMPA_LF composed with LLM_Direct's logged answers judged against
that rebuild's T+.

    python run.py rebuild make                 # rebuild_work/r<r>/: data roots
    python run.py rebuild jobs --phase build   # shell lines: tools and generators
    python run.py rebuild jobs --phase eval    # shell lines: TEMPA_L per (r, pid)
    python run.py rebuild compose              # TEMPA_LF per rebuild
    python run.py rebuild report               # -> results/rebuild.csv

The tools and generators land in tools/rebuild/r<r>/; rebuild_work/ only links
the benchmark to them and is not tracked.
"""
from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd

from src.experiments._common import IDS, ORDER, load_problem
from src.experiments.augment import _key, _suite, tplus_keys
from src.experiments.compose import compose as compose_lf
from src.experiments.compose import escalated, judged_direct
from src.experiments.results_io import read_events, write_events
from src.runner.testing import run_tests

ROOT = Path(__file__).resolve().parents[2]
BENCH, WORK, TOOLS = ROOT / "benchmark", ROOT / "rebuild_work", ROOT / "tools" / "rebuild"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
CS1 = ORDER[:5]
REBUILDS = (1, 2)


def make() -> None:
    for r in REBUILDS:
        for pid in ORDER:
            d = WORK / f"r{r}" / pid
            d.mkdir(parents=True, exist_ok=True)
            links = {n: BENCH / pid / n for n in ("problem.json", "buggy", "correct")}
            if pid in CS1:                     # the generator Amplify writes, tracked
                links["amplified"] = TOOLS / f"r{r}" / pid / "amplified"
                links["amplified"].mkdir(parents=True, exist_ok=True)
            for name, target in links.items():
                if not (d / name).exists():
                    (d / name).symlink_to(target)


def jobs(phase: str) -> None:
    for r in REBUILDS:
        base, tools = f"rebuild_work/r{r}", f"tools/rebuild/r{r}"
        for pid in ORDER:
            if phase == "build":
                for m in MODELS:
                    if not (TOOLS / f"r{r}" / pid / m / "cost.json").exists():
                        print(f"python3 run.py build --problem {pid} --model {m} "
                              f"--tools-root {tools}")
            else:                               # both builders share one CSV: one line
                amp = " --amplified" if pid in CS1 else ""
                print(" && ".join(
                    f"python3 run.py compare --problem {pid} --data-root {base} "
                    f"--tools-root {tools} --ver rebuild/r{r} --model {m} --no-llm{amp}"
                    for m in MODELS))
        if phase == "build":
            for m in MODELS:                    # asks the builder only where none exists
                print(f"python3 run.py augment amplify --model {m} --root {base}")


def compose() -> None:
    for r in REBUILDS:
        ver = f"rebuild/r{r}"
        for pid in ORDER:
            for m in MODELS:
                local = read_events(ver, pid, "tempa_l", m)
                if pid in CS1:                  # Direct's answer under this rebuild's T+
                    prob = load_problem(pid, str(WORK / f"r{r}"), m)
                    need = escalated(local)
                    direct = judged_direct(need, pid, m, prob, BENCH / pid / "buggy")
                    direct += [x for x in local if x not in need]
                else:                           # T+ = T: the campaign's verdicts hold
                    direct = read_events("", pid, "direct_llm", m)
                write_events(ver, pid, "tempa_lf", compose_lf(local, direct))
            print(f"r{r} {IDS[pid]}: composed", flush=True)


def _cost(r: int, pid: str, m: str) -> tuple[float, int]:
    root = ROOT / "tools" if r == 0 else TOOLS / f"r{r}"
    c = json.loads((root / pid / m / "cost.json").read_text())
    usd, rules = c["usd"], c["rules"]
    gen = (BENCH if r == 0 else root) / pid / "amplified" / m / "cost.json"
    return usd + (json.loads(gen.read_text())["usd"] if gen.exists() else 0.0), rules


def report() -> pd.DataFrame:
    rows = []
    for r in (0, *REBUILDS):
        ver = "" if r == 0 else f"rebuild/r{r}"
        for pid in ORDER:
            for m in MODELS:
                lf = read_events(ver, pid, "tempa_lf", m)
                l_ = {x["Buggy"]: x["Fixed"] for x in read_events(ver, pid, "tempa_l", m)}
                held = {}
                if pid in CS1:                  # held-out, less this rebuild's T_amp too
                    root = BENCH if r == 0 else WORK / f"r{r}"
                    amp = root / pid / "amplified" / m / "tests.json"
                    seen = tplus_keys(pid) | {_key(t) for t in json.loads(amp.read_text())}
                    prob = load_problem(pid)
                    extra = _suite(pid)["tests"][len(prob["tests"]):]
                    suite = dict(prob, tests=prob["tests"]
                                 + [t for t in extra if _key(t) not in seen])
                    codes = {x["Patch"] for x in lf if x["Fixed"]}
                    with ThreadPoolExecutor(16) as ex:
                        held = dict(zip(codes, ex.map(lambda c: run_tests(c, suite).all_pass, codes)))
                usd, rules = _cost(r, pid, m)
                for x in lf:
                    ok = bool(x["Fixed"])
                    h = ok and (held[x["Patch"]] if pid in CS1 else True)
                    rows.append({"rebuild": r, "pid": pid, "model": m, "buggy": x["Buggy"],
                                 "l_fixed": bool(l_.get(x["Buggy"])), "fixed": ok, "held": h,
                                 "rps": x["RPS"] if ok else None, "api_usd": x["$API"],
                                 "build_usd": usd, "rules": rules})
        print(f"r{r}: judged", flush=True)
    d = pd.DataFrame(rows)
    d.to_csv(ROOT / "results" / "rebuild.csv", index=False)
    g = d.groupby(["model", "rebuild"])
    rep = pd.DataFrame({
        "RR_L": 100 * g.l_fixed.mean(), "RR": 100 * g.fixed.mean(),
        "RR_held": 100 * g.held.mean(), "RPS": g.rps.mean(),
        "RR_0.25": 100 * g.apply(lambda x: (x.held & (x.rps.astype(float) <= .25)).mean()),
        "api_usd": g.api_usd.sum(),
        "build_usd": g.apply(lambda x: x.drop_duplicates("pid").build_usd.sum()),
        "rules": g.apply(lambda x: x.drop_duplicates("pid").rules.sum())})
    print(rep.round(3).to_string())
    print(rep.groupby("model").agg(["mean", "std", "min", "max"]).round(3).T.to_string())
    return d


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py rebuild")
    ap.add_argument("action", choices=["make", "jobs", "compose", "report"])
    ap.add_argument("--phase", choices=["build", "eval"], default="build")
    args = ap.parse_args(argv)
    if args.action == "jobs":
        jobs(args.phase)
    else:
        {"make": make, "compose": compose, "report": report}[args.action]()
    return 0
