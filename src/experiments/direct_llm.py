"""`run.py direct` — TEMPA's own fallback query, sent for every submission.

The matched per-submission baseline. It is exactly the call TEMPA_LF escalates
with -- the same prompt, the same information (description, example tests, the
buggy program, its failing tests, and the minimum-edit reference program
pi(b)), the same model, one call, the same acceptance by the test oracle -- but
issued for every buggy program instead of only for those the local tool cannot
serve. TEMPA_LF against this arm therefore differs in one design choice alone,
the local-first architecture, which PyDex (different prompt, three retrieved
exemplars, ten samples) cannot isolate.

Querying and judging are separate steps, because the tests run under a wall
clock and judging on a loaded machine turns slow passes into failures:

    python run.py direct --problem P --model M            # query; keeps every candidate
    python run.py direct --problem P --model M --revalidate   # judge on a quiet machine

    results/<ver>/<p_id>/direct_llm_<model>.json   candidates and their call accounting
    results/<ver>/<p_id>/direct_llm.csv            one row per buggy submission
    results/<ver>/<p_id>/summary.csv               upserted (Approach=LLM_Direct, Model)
"""
from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from src.core.fallback import fallback_repair
from src.experiments._common import load_env, load_pool, load_problem
from src.experiments.results_io import (ROOT, build_overall, event_row,
                                        summarize_events, upsert_summary,
                                        write_events)
from src.runner.testing import run_tests
from src.utils.metrics import rps


def _candidates(ver: str, pid: str, model: str) -> Path:
    return ROOT / "results" / ver / pid / f"direct_llm_{model}.json"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py direct")
    ap.add_argument("--problem", required=True)
    ap.add_argument("--model", default="claude-sonnet-5")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--data-root", default="benchmark")
    ap.add_argument("--amplified", action="store_true",
                    help="accept against T+, the builder's amplified suite (R1-R5)")
    ap.add_argument("--ver", default="")
    ap.add_argument("--revalidate", action="store_true",
                    help="judge the stored candidates again; no model call")
    args = ap.parse_args(argv)

    prob = load_problem(args.problem, args.data_root,
                        args.model if args.amplified else None)
    files = sorted((Path(args.data_root) / args.problem / "buggy").glob("*.py"))
    store = _candidates(args.ver, args.problem, args.model)

    if not args.revalidate:
        load_env()
        correct = load_pool(args.problem, "correct", args.data_root)

        def ask(f: Path) -> tuple[str, dict]:
            try:
                fb = fallback_repair(f.read_text(), prob, correct, model=args.model)
            except Exception as e:             # noqa: BLE001 - a failed call is a miss
                print(f"  {f.stem}: {type(e).__name__}: {e}")
                return f.stem, {"candidate": None, "error": f"{type(e).__name__}"}
            return f.stem, {"candidate": fb.candidate, "in": fb.in_tokens,
                            "out": fb.out_tokens, "s": fb.seconds, "usd": fb.usd}

        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            got = dict(ex.map(ask, files))
        store.parent.mkdir(parents=True, exist_ok=True)
        store.write_text(json.dumps(got))
    got = json.loads(store.read_text())

    def judge(f: Path) -> dict:
        c = got.get(f.stem, {})
        cand = c.get("candidate")
        res = run_tests(cand, prob) if cand else None
        ok = bool(res and res.error is None and res.total and res.passed == res.total)
        src = f.read_text()
        return event_row(f.stem, args.model, "llm" if ok else "none", ok,
                         cand if ok else None, rps(src, cand) if ok else None,
                         att_api=c.get("s", 0.0), in_tok=c.get("in", 0),
                         out_tok=c.get("out", 0), api_usd=c.get("usd", 0.0))

    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        rows = list(ex.map(judge, files))
    write_events(args.ver, args.problem, "direct_llm", rows)
    summ = summarize_events("LLM_Direct", args.model, rows)
    upsert_summary(args.ver, args.problem, summ)
    build_overall(args.ver)
    print(f"[{args.problem}] LLM_Direct ({args.model}): RR={100 * summ['RR']:.2f}% "
          f"RPS={summ['RPS']:.4f} $={summ['$API']:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
