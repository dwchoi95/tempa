"""Rule sources compared like for like: the builder's rules (LLM), no rules, and the
non-LLM baseline Refazer, each in the same frozen tool (TEMPA_L: rules, then transplant, accepting on T+) and in the deployed
tool recomposed with the logged LLM_Direct query as fallback (gate 1.0 and 0.25),
exactly as src/experiments/ablation.py recomposes its arms. No model call.

    python3 results/checks/baselines/analyze.py [SOURCE...]   -> rows.csv, metrics.csv, mcnemar.csv

Each patch's held-out verdict is cached in heldout_cache.json (not tracked); without it, the
patches are run on the held-out suite again, which takes about 15 s.
"""
import csv, json, math, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.experiments import ablation                       # noqa: E402
from src.experiments._common import IDS, ORDER             # noqa: E402
from src.experiments.augment import _suite                 # noqa: E402
from src.runner.testing import run_tests                   # noqa: E402

HERE = Path(__file__).resolve().parent
CS1 = ORDER[:5]
TAUS = (0.1, 0.25, 0.5)
SOURCES = sys.argv[1:] or ["refazer"]
csv.field_size_limit(10**9)


def compose(local: dict, direct: dict, gate: float) -> dict:
    saved = ablation.RPS_GATE
    ablation.RPS_GATE = gate
    try:
        return ablation._compose(local, direct)
    finally:
        ablation.RPS_GATE = saved


def unseen() -> set:
    return {(r["pid"], r["buggy"]) for r in csv.DictReader(
        open(HERE / "worked_pairs.csv")) if r["worked"] == "False"}


def builder_rules(v: dict) -> bool:
    """A local repair whose rules include one that is not always-on."""
    if v["source"] != "rules":
        return False
    names = json.loads(v["rules"] or "[]")
    return any(not n.startswith("generic_") for n in names)


def main():
    cache_f = HERE / "heldout_cache.json"
    cache = json.loads(cache_f.read_text()) if cache_f.exists() else {}
    rows = []
    for pid in ORDER:
        direct = ablation._log(pid, "direct_llm")
        local = {"LLM rules": ablation._log(pid, "tempa_l"),
                 "no rules": ablation._log(pid, "tempa_l_fw")}
        for s in SOURCES:
            f = HERE / f"baseline_{s}" / pid / "tempa_l.csv"
            if f.exists():
                local[s] = ablation._log(f"checks/baselines/baseline_{s}/{pid}", "tempa_l")
        arms = {}
        for name, lo in local.items():
            arms[f"{name} | local"] = lo
            arms[f"{name} | +fallback"] = compose(lo, direct, 1.0)
            arms[f"{name} | +fallback gate 0.25"] = compose(lo, direct, 0.25)
        if pid in CS1:
            suite = _suite(pid)
            todo = sorted({v["patch"] for a in arms.values() for v in a.values()
                           if v["fixed"] and v["patch"] not in cache.get(pid, {})})
            with ThreadPoolExecutor(16) as ex:
                got = dict(zip(todo, ex.map(lambda p: run_tests(p, suite).all_pass, todo)))
            cache.setdefault(pid, {}).update(got)
            cache_f.write_text(json.dumps(cache))
        for arm, got in arms.items():
            for (model, buggy), v in got.items():
                held = (cache[pid][v["patch"]] if pid in CS1 else True) if v["fixed"] else False
                rows.append({"arm": arm, "pid": pid, "model": model, "buggy": buggy,
                             "fixed": v["fixed"], "held": held, "rps": v["rps"],
                             "source": v["source"], "builder_rule": builder_rules(v) if v["fixed"] else False,
                             "query": float(v.get("usd") or 0) > 0})
        print(f"{IDS[pid]}: {len(arms)} arms", flush=True)
    # like for like: keep a program only where every arm has its row (a run still
    # in progress lacks some)
    have = {}
    for r in rows:
        have.setdefault((r["pid"], r["model"], r["buggy"]), set()).add(r["arm"])
    n_arms = len({r["arm"] for r in rows})
    missing = sorted({k for k, a in have.items() if len(a) < n_arms})
    if missing:
        print("dropped from every arm (some arm lacks them):", missing)
    rows = [r for r in rows if len(have[(r["pid"], r["model"], r["buggy"])]) == n_arms]
    with open(HERE / "rows.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, rows[0].keys()); w.writeheader(); w.writerows(rows)
    report(rows)


def ok(r, t):
    return r["held"] and r["rps"] is not None and float(r["rps"]) <= t


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


def report(rows):
    U = unseen()
    by = {}
    for r in rows:
        by.setdefault((r["arm"], r["model"]), []).append(r)
    out = []
    for (arm, model), g in by.items():
        for sub, gg in (("all", g), ("unseen", [r for r in g if (r["pid"], r["buggy"]) in U])):
            n = len(gg)
            row = {"subset": sub, "arm": arm, "model": model, "n": n,
                   "RR": 100 * sum(r["fixed"] for r in gg) / n,
                   "RR_held": 100 * sum(r["held"] for r in gg) / n,
                   "rule_repairs": sum(r["builder_rule"] for r in gg),
                   "queries": sum(r["query"] for r in gg)}
            for t in TAUS:
                row[f"RR_{t}"] = 100 * sum(ok(r, t) for r in gg) / n
            out.append(row)
    with open(HERE / "metrics.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, out[0].keys()); w.writeheader(); w.writerows(out)
    for row in out:
        print(f"{row['subset']:6s} {row['arm']:34s} {row['model']:16s} n={row['n']:5d} "
              f"RR={row['RR']:5.1f} held={row['RR_held']:5.1f} rules={row['rule_repairs']:4d} "
              f"q={row['queries']:5d} RR.1={row['RR_0.1']:5.1f} RR.25={row['RR_0.25']:5.1f} RR.5={row['RR_0.5']:5.1f}")
    # paired exact McNemar: each rule source against the builder's rules, in the same setting
    idx = {(r["arm"], r["model"], r["pid"], r["buggy"]): r for r in rows}
    mc = []
    for sub in ("all", "unseen"):
        for setting in ("local", "+fallback", "+fallback gate 0.25"):
            for other in ["no rules"] + SOURCES:
                for model in ("claude-sonnet-5", "gpt-5.4-mini"):
                    keys = [(p, b) for (a, m, p, b) in idx if a == f"LLM rules | {setting}" and m == model
                            and (sub == "all" or (p, b) in U)]
                    if not keys or (f"{other} | {setting}", model, *keys[0]) not in idx:
                        continue
                    for t in TAUS:
                        x = sum(ok(idx[(f"LLM rules | {setting}", model, p, b)], t)
                                and not ok(idx[(f"{other} | {setting}", model, p, b)], t) for p, b in keys)
                        y = sum(ok(idx[(f"{other} | {setting}", model, p, b)], t)
                                and not ok(idx[(f"LLM rules | {setting}", model, p, b)], t) for p, b in keys)
                        mc.append({"subset": sub, "setting": setting, "vs": other, "model": model,
                                   "tau": t, "llm_only": x, "other_only": y, "p_exact": exact_p(x, y)})
    with open(HERE / "mcnemar.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, mc[0].keys()); w.writeheader(); w.writerows(mc)


if __name__ == "__main__":
    main()
