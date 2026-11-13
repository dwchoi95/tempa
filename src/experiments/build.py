"""`run.py build` — synthesize tools/<p_id>/<model>/{fixer.rules, cost.json}.

Stage 1 (local, no LLM cost) selects the build samples; Stage 2
calls the builder model. The same selection feeds every model.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from src.core.repair import SearchBudget
from src.core.synthesis import build, select_sample_pairs
from src.experiments._common import load_env, load_pool, load_problem


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="run.py build")
    ap.add_argument("--problem", required=True, help="problem id, e.g. refactory_q1")
    ap.add_argument("--model", default=["claude-sonnet-5", "gpt-5.4-mini"], nargs="+",
                    help="builder model(s)")
    ap.add_argument("--r-max", type=int, default=3)
    ap.add_argument("--data-root", default="benchmark")
    ap.add_argument("--tools-root", default="tools",
                    help="where to write <p_id>/<model>/; use a separate root to "
                         "compare configurations without clobbering the campaign")
    ap.add_argument("--batch", action="store_true",
                    help="send each builder query through the provider's batch API (half price)")
    args = ap.parse_args(argv)
    load_env()
    tool = "fixer.rules"
    todo = []                        # resumable across parallel runners
    for model in args.model:
        d = Path(args.tools_root) / args.problem / model
        if ((d / "cost.json").exists() and (d / tool).exists()) or (d / ".building").exists():
            print(f"{args.problem} [{model}]: built or being built, skipped")
            continue
        d.mkdir(parents=True, exist_ok=True)
        (d / ".building").touch()
        todo.append(model)
    if not todo:
        return 0
    args.model = todo

    prob = load_problem(args.problem, args.data_root)
    buggy = load_pool(args.problem, "buggy", args.data_root)
    correct = load_pool(args.problem, "correct", args.data_root)

    pairs = select_sample_pairs(buggy, correct)
    samples = [b for b, _f, _n in pairs]
    fixes = [f for _b, f, _n in pairs]
    print(f"{args.problem}: {len(buggy)} buggy, {len(correct)} correct → "
          f"{len(samples)} (buggy→fixed) pairs, one per cluster")

    budget = SearchBudget()
    for model in args.model:
        res = build(prob, samples, model=model, r_max=args.r_max,
                    budget=budget, sample_fixes=fixes, batch=args.batch,
                    out_path=Path(args.tools_root) / args.problem / model / tool)
        print(f"  [{model}] rules={res.rules} coverage={res.coverage:.0%} "
              f"rounds={res.rounds} cost=${res.usd:.4f} → {res.path}")
        (Path(args.tools_root) / args.problem / model / ".building").unlink(missing_ok=True)
    return 0
