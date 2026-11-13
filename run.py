#!/usr/bin/env python3
"""TEMPA entrypoint.

Dispatch only: every subcommand forwards to a driver in ``src/experiments/``.
No experiment logic lives here, so drivers stay independently runnable and
testable.

    python run.py build   --problem refactory_q1 --model claude-sonnet-5
    python run.py compare --problem refactory_q1 --model claude-sonnet-5 --amplified
    python run.py stats
    python run.py --list
"""
from __future__ import annotations

import argparse
import importlib

# subcommand -> (module under src.experiments, entry function)
COMMANDS = {
    # TEMPA
    "build": ("build", "main"),            # synthesize tools/<pid>/<model>/fixer.rules
    "augment": ("augment", "main"),        # amplified (TEMPA) and held-out (evaluation) suites
    "compare": ("compare", "main"),        # TEMPA_L and TEMPA_LF (and -Syn) on one assignment
    "repair": ("repair", "main"),          # repair one submission (tool + fallback)
    # baselines
    "pydex": ("pydex_run", "main"),        # PyDex and PyDex_PC
    "direct": ("direct_llm", "main"),      # LLM_Direct: TEMPA's fallback query for every submission
    "refactory": ("refactory_results", "main"),            # collect a Refactory run
    "refactory-published": ("refactory_published", "main"),  # its published R1-R5 figures
    # analyses
    "stats": ("stats_report", "main"),     # Wilson intervals + exact McNemar
    "pool": ("pool_ablation", "main"),     # the Synthesize ablation as the pool thins
    "thin-pool": ("pool_ablation", "split_main"),  # the same on Section 5.5's splits
    "search-size": ("search_size", "main"),  # candidates validated per program, and determinism
    "sensitivity": ("sensitivity", "main"),  # Theorem 4.3: overfitting against n and the budget
    "rebuild": ("rebuild", "main"),        # build every tool again, twice, and re-evaluate
    "cluster-once": ("cluster_once", "main"),  # one query per Select cluster, spread by transplant
    "compose": ("compose", "main"),        # TEMPA_LF from the tool's run and the logged query
    "ablation": ("ablation", "main"),      # what the rules and T+ buy TEMPA_LF, from the logs
    "pydex-oracle": ("pydex_oracle", "main"),  # PyDex accepting T+, and its K curve
    "splits": ("splits", "main"),          # build on earlier submissions, repair later ones
    "split-fallback": ("split_fallback", "main"),  # the fallback with a split's own pool (paid)
    # the paper (dev branch only)
    "tables": ("tables", "main"),
    "numbers": ("numbers", "main"),
    "figures": ("figures", "main"),
}


def main(argv: list[str] | None = None) -> int:
    # a driver that is not in this checkout (the paper's, on main) is not offered
    commands = {k: v for k, v in COMMANDS.items() if _importable(v[0])}
    ap = argparse.ArgumentParser(prog="run.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", nargs="?", choices=list(commands), help="stage to run")
    ap.add_argument("--list", action="store_true", help="list available drivers")
    args, rest = ap.parse_known_args(argv)

    if args.list or not args.command:
        print("commands:")
        for name, (mod, fn) in commands.items():
            print(f"  {name:20s} -> src/experiments/{mod}.py:{fn}")
        return 0

    mod_name, fn_name = commands[args.command]
    mod = importlib.import_module(f"src.experiments.{mod_name}")
    return int(getattr(mod, fn_name)(rest) or 0)


def _importable(mod: str) -> bool:
    import importlib.util
    return importlib.util.find_spec(f"src.experiments.{mod}") is not None


if __name__ == "__main__":
    raise SystemExit(main())
