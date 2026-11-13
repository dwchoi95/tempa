"""Does the builder's rule layer matter when the reference pool is thin?

The tool is held fixed; only the pool the transplant may draw on at repair time
is restricted. That isolates the substrate's dependence on pool depth without
paying to rebuild a tool per pool size. A full cold start would also rebuild,
and costs money; this does not.

Two things this gets right that the obvious version does not:

* **Submissions the builder saw are excluded.** Roughly half of each
  assignment's buggy pool ends up in the build set, and on those the authored
  rules are answering a program they were written from. Scoring them measures
  memorisation, not the layer.
* **Pool draws are repeated.** For k > 0 the pool is a sample of the correct
  programs, and one draw is one accident; each k is run over several seeds.

For each pool size k we run two arms over the same submissions:
  full   = the frozen tool as shipped (builder rules + always-on + transplant)
  fw     = the same tool with the builder's rules removed
"""
import argparse, json, random, time
from pathlib import Path

import pandas as pd

from src.core.reference_repair import ReferenceIndex, local_repair
from src.core.repair import SearchBudget
from src.core.synthesis import load_fixer
from src.experiments._common import IDS, ORDER, load_pool, load_problem, tool_path
from src.utils.metrics import rps

ROOT = Path(__file__).resolve().parents[2]
MODEL = "claude-sonnet-5"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--per-problem", type=int, default=15)
    ap.add_argument("--ks", default="0,1,2,5,-1")   # -1 = the whole pool
    ap.add_argument("--seeds", type=int, default=3, help="pool draws per k > 0")
    ap.add_argument("--out", default="")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--problems", default="",
                    help="comma-separated ids to run (default: all); for running "
                         "assignments in parallel and concatenating the outputs")
    ap.add_argument("--amplified", action="store_true",
                    help="accept against T+, the builder's amplified suite (R1-R5)")
    args = ap.parse_args(argv)
    ks = [int(x) for x in args.ks.split(",")]
    from src.core.synthesis import select_sample_pairs
    budget = SearchBudget()
    rows = []
    only = set(args.problems.split(",")) if args.problems else None
    for pid in ORDER:
        if only and pid not in only:
            continue
        prob = load_problem(pid, str(ROOT / "benchmark"), MODEL if args.amplified else None)
        correct = load_pool(pid, "correct", str(ROOT / "benchmark"))
        buggy = load_pool(pid, "buggy", str(ROOT / "benchmark"))
        names = sorted(p.stem for p in (ROOT / "benchmark" / pid / "buggy").glob("*.py"))
        # the builder was shown roughly half of these; scoring them would
        # measure whether a rule remembers the program it was written from.
        # Submissions are deduplicated by text, so one source can carry several
        # names and every one of them has to go, not just the last.
        by_src: dict[str, list[str]] = {}
        for src_text, name in zip(buggy, names):
            by_src.setdefault(src_text, []).append(name)
        seen = {n for b, _f, _n in select_sample_pairs(buggy, correct)
                for n in by_src.get(b, ())}
        pool_of = [n for n in names if n not in seen]
        rng = random.Random(args.seed)
        pick = (pool_of if len(pool_of) <= args.per_problem
                else rng.sample(pool_of, args.per_problem))
        srcs = [(n, (ROOT / "benchmark" / pid / "buggy" / f"{n}.py").read_text()) for n in pick]
        rules_all = load_fixer(tool_path(pid, MODEL, str(ROOT / "tools")))
        rules_fw = [r for r in rules_all if r.name.startswith("generic_")]
        for k in ks:
            # k = 0 and the whole pool are deterministic; only a sampled pool
            # needs repeating
            seeds = [args.seed] if k <= 0 else range(args.seeds)
            for sd in seeds:
                if k < 0:
                    pool = correct
                elif k == 0:
                    pool = []
                else:
                    pool = random.Random(sd).sample(correct, min(k, len(correct)))
                index = ReferenceIndex(pool) if pool else ReferenceIndex([])
                for arm, rules in (("full", rules_all), ("fw", rules_fw)):
                    t0 = time.time()
                    for name, src in srcs:
                        res = local_repair(src, prob, rules, index, budget)
                        rows.append({"pid": IDS[pid], "k": k, "seed": sd,
                                     "arm": arm, "buggy": name,
                                     "fixed": bool(res.repaired),
                                     "source": res.source if res.repaired else "none",
                                     "rps": rps(src, res.patch) if res.repaired else None})
                    print(f"  {IDS[pid]:<3} k={k:<3} s{sd} {arm:<5} {len(srcs)} subs "
                          f"in {time.time()-t0:5.1f}s", flush=True)
    if args.out:
        open(args.out, "w").write(json.dumps(rows))
    print(f"{len(rows)} rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


def split_main(argv: list[str] | None = None) -> int:
    """`run.py thin-pool` — the same question at the scale of Section 5.5.

    A new assignment has a tool built from its first submissions and a pool of
    only the few correct programs submitted so far. Here the tools built from
    the first 10% of each class (tools/splits/<scheme>/f10) repair that split's
    test programs, which no builder saw, with a pool of the first k correct
    programs in the split's order (no draw, so no seed), against the split's
    acceptance suite. Both arms escalate on the gate of TEMPA_LF, and the
    fallback's answer is LLM_Direct's logged one, judged against the same suite.

        python run.py thin-pool --scheme s0 --problem P   # -> results/thin_pool/
    """
    from concurrent.futures import ThreadPoolExecutor
    from src.experiments.augment import _suite
    from src.runner.testing import run_tests
    ap = argparse.ArgumentParser(prog="run.py thin-pool")
    ap.add_argument("--scheme", default="s0")
    ap.add_argument("--problem", required=True)
    ap.add_argument("--ks", default="1,2,5")
    args = ap.parse_args(argv)
    pid, scheme, ks = args.problem, args.scheme, [int(k) for k in args.ks.split(",")]
    work = ROOT / "splits_work"
    entry = json.loads((work / "manifest.json").read_text())[scheme][pid]
    test, order = entry["test"], entry["train"]["10"]["correct"]
    held = _suite(pid) if pid in ORDER[:5] else None
    rows, budget = [], SearchBudget()
    for m in ("claude-sonnet-5", "gpt-5.4-mini"):
        data = work / scheme / "f10" / (f"eval_amplified/{m}" if held else "eval")
        prob = load_problem(pid, str(data))
        rules_all = load_fixer(tool_path(pid, m, str(ROOT / "tools" / "splits" / scheme / "f10")))
        arms = (("full", rules_all), ("fw", [r for r in rules_all if r.name.startswith("generic_")]))
        direct = json.loads((ROOT / "results" / pid / f"direct_llm_{m}.json").read_text())
        srcs = {s: (data / pid / "buggy" / f"{s}.py").read_text() for s in test}

        def judge(s):                          # LLM_Direct's answer under this suite
            c = direct[s].get("candidate") or ""
            ok = bool(c) and run_tests(c, prob).all_pass
            return s, (c if ok else None, direct[s].get("usd", 0.0))
        with ThreadPoolExecutor(8) as ex:
            fb_class = dict(ex.map(judge, test))
        for k in ks:
            # the fallback queried with this k-program pool (split-fallback), when
            # it has been; LLM_Direct's whole-class answer otherwise
            own = ROOT / "results" / "thin_pool" / "fallback" / f"{scheme}_{pid}_{m}_k{k}.json"
            if own.exists():
                direct = json.loads(own.read_text())
                with ThreadPoolExecutor(8) as ex:
                    fb = dict(ex.map(judge, [s for s in test if s in direct]))
                fb = {s: fb.get(s, (None, 0.0)) for s in test}
            else:
                fb = fb_class
            pool = [(data / pid / "correct" / f"{s}.py").read_text() for s in order[:k]]
            index = ReferenceIndex(pool)
            for arm, rules in arms:
                for s, src in srcs.items():
                    r = local_repair(src, prob, rules, index, budget)
                    pr = rps(src, r.patch) if r.repaired else None
                    esc = not (r.repaired and pr <= 1.0)
                    fc, usd = fb[s]
                    use_fb = esc and fc is not None and (pr is None or rps(src, fc) < pr)
                    patch = fc if use_fb else r.patch
                    rows.append({"scheme": scheme, "pid": IDS[pid], "model": m, "k": k,
                                 "pool": len(pool), "arm": arm, "buggy": s,
                                 "fixed": r.repaired, "source": r.source, "rps": pr,
                                 "tried": r.tried, "cut": r.cut, "esc": esc,
                                 "lf_fixed": patch is not None,
                                 "lf_rps": rps(src, patch) if patch else None,
                                 "usd": usd if esc else 0.0, "patch": patch or ""})
                print(f"{scheme} {IDS[pid]} [{m}] k={k} {arm}: "
                      f"{sum(x['fixed'] for x in rows[-len(srcs):])}/{len(srcs)}", flush=True)
    d = pd.DataFrame(rows)
    if held is not None:                      # held-out verdict per distinct patch
        codes = sorted(set(d.patch) - {""})
        with ThreadPoolExecutor(8) as ex:
            ok = dict(zip(codes, ex.map(lambda c: run_tests(c, held).all_pass, codes)))
        d["held"] = d.patch.map(lambda c: bool(c) and ok[c])
    out = ROOT / "results" / "thin_pool"
    out.mkdir(parents=True, exist_ok=True)
    d.drop(columns="patch").to_csv(out / f"{scheme}_{pid}.csv", index=False)
    return 0
