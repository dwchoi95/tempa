"""`run.py pydex` — the PyDex baseline (paper-faithful semantic phase) over one
problem, stored in the unified CSV format:

    results/<ver>/<p_id>/pydex.csv      one row per truly-buggy submission
    results/<ver>/<p_id>/pydex_pc.csv   the same run re-priced under provider
                                        prompt caching (PyDex_PC)
    results/<ver>/<p_id>/summary.csv    upserted rows for both approaches

Per submission: one Fig.6 zero-shot prompt (Fig.7 few-shot automatically when a
pairs.json bank exists) -> K sampled candidates -> full-suite oracle -> the
min-token-edit-distance survivor. ALL K calls are billed and timed, including
oracle-rejected candidates. ATT_api is the summed call latency; ATT_cpu is the
remaining wall time (candidate executions, retrieval, selection).

PyDex_PC is a documented-rules UPPER BOUND on what provider caching could
deliver for these exact queries: cross-submission reuse is impossible (the buggy-first
layout shares a ~13-token leading prefix), so the only cacheable structure is
the K identical prompts *within* one submission — modeled as first call full
price, the remaining K-1 prompts read at 0.1x (write 1.25x on Anthropic, free
on pre-5.6 OpenAI), gated on each provider's 1,024-token cacheable minimum. The PyDex arm itself is billed
from raw token counts at full rates, so no incidental provider cache hit can
leak a discount into the uncached baseline.
"""
from __future__ import annotations

import argparse
import time
from pathlib import Path

from baselines.pydex.pydex import K_DEFAULT, ShotBank, repair
from src.experiments._common import load_env, load_problem
from src.experiments.results_io import (event_row, read_events, summarize_events,
                                        upsert_summary, write_events)
from src.utils.metrics import PRICES, rps

CACHE_MIN = {"claude-sonnet-5": 1024, "gpt-5.4-mini": 1024}  # cacheable minimums
CACHE_READ = 0.1
CACHE_WRITE = {"claude-sonnet-5": 1.25,
               "gpt-5.4-mini": 0.0}       # gpt-5.4 family: writes free


def _existing_stems(ver: str, pid: str, model_label: str) -> set[str]:
    """Submissions this model has already been queried on for this problem."""
    return {str(r["Buggy"]) for r in read_events(ver, pid, "pydex", model_label)}


def _revalidate(args) -> int:
    import json
    from concurrent.futures import ThreadPoolExecutor
    from src.runner.testing import run_tests
    prob = load_problem(args.problem, args.data_root)
    rows = read_events(args.ver, args.problem, "pydex", args.model)
    keep = {str(r["Buggy"]) for r in rows}
    with ThreadPoolExecutor(8) as ex:
        ok = list(ex.map(lambda r: bool(r["Fixed"]) and run_tests(str(r["Patch"]), prob).all_pass,
                         rows))
    lost = sorted(str(r["Buggy"]) for r, o in zip(rows, ok) if r["Fixed"] and not o)
    for stem in ("pydex", "pydex_pc"):
        rs = [r for r in read_events(args.ver, args.problem, stem, args.model)
              if str(r["Buggy"]) in keep]
        for r in rs:
            if str(r["Buggy"]) in lost:
                r.update(Fixed=False, Source="none", Patch=None, RPS=None)
        write_events(args.ver, args.problem, stem, rs)
        upsert_summary(args.ver, args.problem, summarize_events(
            "PyDex" if stem == "pydex" else "PyDex_PC", args.model, rs))
    f = Path("results") / args.ver / args.problem / "pydex_requery.json"
    todo = json.loads(f.read_text()) if f.exists() else {}
    todo[args.model] = sorted(set(todo.get(args.model, [])) | set(lost))
    f.write_text(json.dumps(todo, indent=1))
    print(f"{args.problem} [{args.model}]: {len(lost)} picks fail T now")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="run.py pydex")
    ap.add_argument("--problem", required=True)
    ap.add_argument("--model", default="claude-sonnet-5")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--k", type=int, default=K_DEFAULT,
                    help="candidates per prompt (paper: 10)")
    ap.add_argument("--data-root", default="benchmark")
    ap.add_argument("--ver", default="",
                    help="optional subdirectory under results/; empty means "
                         "results/ itself, which is where the campaign wrote")
    ap.add_argument("--revalidate", action="store_true",
                    help="judge the stored picks against the current T; no model call. "
                         "A pick that now fails is a miss, and its program is listed in "
                         "pydex_requery.json, since only re-sampling can say what PyDex picks "
                         "instead (a pick that still passes stays the closest survivor)")
    ap.add_argument("--requery", action="store_true",
                    help="query again only the programs --revalidate listed in "
                         "pydex_requery.json, and merge")
    ap.add_argument("--only-missing", action="store_true",
                    help="query only submissions with no row yet for this model, "
                         "and merge; every query costs, so a widened pool should "
                         "not repurchase the answers already on disk")
    args = ap.parse_args(argv)
    if args.revalidate:
        return _revalidate(args)
    load_env()

    prob = load_problem(args.problem, args.data_root)
    data_dir = Path(args.data_root) / args.problem
    files = sorted((data_dir / "buggy").glob("*.py"))
    if args.limit:
        files = files[:args.limit]
    model_label = args.model

    if args.requery:
        import json
        f = Path("results") / args.ver / args.problem / "pydex_requery.json"
        todo = json.loads(f.read_text()) if f.exists() else {}
        want = set(todo.get(model_label, []))
        files = [f_ for f_ in files if f_.stem in want]
        print(f"{args.problem} [{model_label}]: re-querying {len(files)}")
        if not files:
            return 0

    if args.only_missing:
        done = _existing_stems(args.ver, args.problem, model_label)
        skipped = [f for f in files if f.stem in done]
        files = [f for f in files if f.stem not in done]
        print(f"{args.problem} [{model_label}]: {len(skipped)} already on disk, "
              f"{len(files)} to query")
        if not files:
            return 0

    bank = ShotBank(prob, data_dir)
    mode = "few-shot" if bank.entries else "zero-shot"
    pin, pout = PRICES[args.model]
    cache_min = CACHE_MIN.get(args.model, 1024)
    w_mult = CACHE_WRITE.get(args.model, 1.25)

    rows, rows_pc = [], []
    for f in files:
        src = f.read_text()
        t0 = time.time()
        res = repair(src, prob, model=args.model, k=args.k, bank=bank)
        wall = time.time() - t0
        att_api = res.seconds
        att_cpu = max(0.0, wall - att_api)
        pr = rps(src, res.patch) if res.repaired else None
        # PyDex billed from raw tokens at full rates: structurally uncached.
        raw_usd = (res.in_tokens * pin + res.out_tokens * pout) / 1e6
        row = event_row(f.stem, model_label, "llm" if res.repaired else "none",
                        res.repaired, res.patch, pr, att_cpu=att_cpu,
                        att_api=att_api, in_tok=res.in_tokens,
                        out_tok=res.out_tokens, api_usd=raw_usd)
        rows.append(row)

        # PC upper bound: the K identical prompts within this submission —
        # first at full price (+write premium), the rest read at 0.1x.
        pc = dict(row)
        prompt_tok = res.in_tokens / max(1, res.calls)
        if res.calls > 1 and prompt_tok >= cache_min:
            reads = res.calls - 1
            discount = prompt_tok * (pin / 1e6) * (
                reads * (1 - CACHE_READ) - (w_mult - 1.0))
            pc["$API"] = round(max(0.0, raw_usd - max(0.0, discount)), 6)
        rows_pc.append(pc)

    write_events(args.ver, args.problem, "pydex", rows)
    write_events(args.ver, args.problem, "pydex_pc", rows_pc)
    # Summarize what is on disk, not what this pass happened to query: a
    # --only-missing run touches a handful of submissions but the arm's result
    # is still the whole pool.
    all_rows = read_events(args.ver, args.problem, "pydex", model_label)
    all_pc = read_events(args.ver, args.problem, "pydex_pc", model_label)
    upsert_summary(args.ver, args.problem,
                   summarize_events("PyDex", model_label, all_rows))
    upsert_summary(args.ver, args.problem,
                   summarize_events("PyDex_PC", model_label, all_pc))

    n = len(all_rows)
    fixed = sum(r["Fixed"] for r in all_rows)
    usd = sum(r["$API"] for r in all_rows)          # arm total, all on disk
    usd_pc = sum(r["$API"] for r in all_pc)
    spent = sum(r["$API"] for r in rows)            # what this pass bought
    print(f"=== {args.problem} PyDex/{mode} [{model_label}] K={args.k} "
          f"{n} submissions (this pass queried {len(rows)}, ${spent:.4f}) ===")
    print(f"RR={100*fixed/max(1,n):.2f}%  $API={usd:.4f}  PC $API={usd_pc:.4f} "
          f"(cache minimum {cache_min} tok for {model_label})")
    print(f"results -> results/{args.ver}/{args.problem}/")
    return 0
