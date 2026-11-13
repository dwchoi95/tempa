"""`run.py compare` — one deterministic pass over a problem's submission stream.

    results/<ver>/<p_id>/tempa_l.csv      TEMPA_L     (frozen local tool only)
    results/<ver>/<p_id>/tempa_lf.csv     TEMPA_LF    (+ LLM fallback)
    results/<ver>/<p_id>/tempa_l_fw.csv   TEMPA_L_fw  (--framework-only ablation)
    results/<ver>/<p_id>/summary.csv     upserted rows (Approach, Model)

Single-pass derivation (no duplicated LLM calls): every submission runs the
frozen local tool, which is TEMPA_L's outcome unconditionally -- it takes any
patch that passes the tests, which is the same acceptance rule the classical
symbolic baseline uses, so the two stay comparable.

TEMPA_LF spends its one call in two places: on a miss, and on a patch at least
as large as the program it repairs (``rps > RPS_GATE``). Local repair's only
acceptance test is the instructor's suite, so transplant can return a patch
larger than the student's whole program; the gate is where the hybrid decides
that is worth a call. The smaller of the two patches is kept, so escalating can
cost money but never coverage or patch size.

The threshold is a constant rather than a calibrated quantity, and that is a
measured choice. Over 38 candidate rules -- median- or mean-anchored with MAD,
standard-deviation or interquartile spread, bare quantiles, multiples of the
assignment's median, corpus-wide variants, and constants -- repair rate is
identical to four decimals and mean RPS falls monotonically with the escalation
rate, so no setting is best and the choice is a budget. Making the threshold
relative to the assignment measurably does not pay: RPS is already normalized
by program size, and normalizing again per assignment sends calls to the
assignments the tool already handles well.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from src.core.fallback import fallback_repair
from src.core.reference_repair import ReferenceIndex, local_repair
from src.core.repair import SearchBudget
from src.core.synthesis import load_fixer
from src.experiments._common import load_env, load_problem, tool_path
from src.experiments.results_io import (event_row, read_events,
                                        summarize_events, upsert_summary,
                                        write_events)
from src.utils.metrics import rps

# A patch at least as large as the program it repairs is a rewrite, not a
# repair, under any assignment's standards. This is the whole gate.
RPS_GATE = 1.0

def _replayed(problem: str, model: str):
    """LLM_Direct's logged answer for a program, shaped as a fallback result."""
    from types import SimpleNamespace
    rows = {str(r["Buggy"]): r for r in read_events("", problem, "direct_llm", model)}

    def fb(stem: str):
        r = rows[stem]
        ok = bool(r["Fixed"])
        return SimpleNamespace(repaired=ok, patch=r["Patch"] if ok else None,
                               seconds=float(r["ATT_api"]), in_tokens=int(r["InT"]),
                               out_tokens=int(r["OuT"]), usd=float(r["$API"]))
    return fb


def _load_files(args, model_label: str = "") -> list[Path]:
    files = sorted((Path(args.data_root) / args.problem / "buggy").glob("*.py"))
    if args.subset:
        keep = set(json.loads(Path(args.subset).read_text())
                   ["problems"].get(args.problem, []))
        files = [f for f in files if f.stem in keep]
    if getattr(args, "only_missing", False):
        # Widening the pool should not re-run the submissions already measured:
        # the escalation tail on those was paid for once already, and buying it
        # again would both cost money and perturb a recorded result.
        done = {str(r["Buggy"]) for r in
                read_events(args.ver, args.problem, "tempa_l", model_label)}
        before = len(files)
        files = [f for f in files if f.stem not in done]
        print(f"{args.problem} [{model_label}]: {before - len(files)} already "
              f"measured, {len(files)} to run")
    if args.limit:
        files = files[:args.limit]
    return files


def _build_cost(path: Path) -> tuple[float, float]:
    f = path.parent / "cost.json"
    d = json.loads(f.read_text()) if f.exists() else {}
    return float(d.get("build_seconds") or 0.0), float(d.get("usd") or 0.0)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="run.py compare")
    ap.add_argument("--problem", required=True)
    ap.add_argument("--model", default="claude-sonnet-5")
    ap.add_argument("--limit", type=int, default=0, help="0 = all buggy programs")
    ap.add_argument("--no-llm", action="store_true",
                    help="skip fallback/absorption (TEMPA_L only; no API key)")
    ap.add_argument("--replay-fallback", action="store_true",
                    help="answer each escalation with LLM_Direct's logged query, as "
                         "compose does, instead of calling the model")
    ap.add_argument("--granularity", choices=["both", "line", "block"], default="both",
                    help="units the transplant adopts: line hunks, then whole top-level "
                         "statements if none passes (TEMPA), or only one of the two")
    ap.add_argument("--framework-only", action="store_true",
                    help="drop the LLM-authored rules and keep the generic "
                         "library and the transplant, to isolate what the "
                         "build buys; writes to <approach>_fw.csv")
    ap.add_argument("--data-root", default="benchmark")
    ap.add_argument("--amplified", action="store_true",
                    help="accept against T+, the builder's amplified suite (R1-R5)")
    ap.add_argument("--amp-n", type=int, default=None,
                    help="with --amplified, keep only the first N amplified tests")
    ap.add_argument("--max-nodes", type=int, default=None,
                    help="rule-search budget in validated candidates (eta_search)")
    ap.add_argument("--tools-root", default="tools",
                    help="read tools from this root; pair with build's "
                         "--tools-root to evaluate an alternate configuration")
    ap.add_argument("--ver", default="",
                    help="optional subdirectory under results/; empty means "
                         "results/ itself, which is where the campaign wrote")
    ap.add_argument("--gate-mode", default="pool", choices=["pool", "crossfit"],
                    help="pool: one threshold fitted on every calibration "
                         "patch (what a deployment ships). crossfit: each "
                         "submission judged by a threshold fitted with its "
                         "fold held out (no submission influences its own rule)")
    ap.add_argument("--subset", default="",
                    help="JSON manifest of submission ids; restricts the pass to its "
                         "sampled submissions for this problem")
    ap.add_argument("--only-missing", action="store_true",
                    help="run only submissions with no row yet for this model, "
                         "and merge into what is already on disk")
    args = ap.parse_args(argv)
    if not args.no_llm:
        load_env()

    prob = load_problem(args.problem, args.data_root,
                        args.model if args.amplified else None)
    if args.amp_n is not None and "n_instructor" in prob:
        prob = dict(prob, tests=prob["tests"][:prob["n_instructor"] + args.amp_n])
    model_label = args.model
    files = _load_files(args, model_label)
    if not files:
        print(f"{args.problem}: no submissions selected, nothing to run")
        return 0
    correct = [f.read_text() for f in
               sorted((Path(args.data_root) / args.problem / "correct").glob("*.py"))]

    frozen_path = tool_path(args.problem, args.model, args.tools_root)
    frozen_rules = load_fixer(frozen_path)
    if args.framework_only:
        # What the build buys, isolated: the generic library and the transplant
        # are the same code either way, so removing only the authored rules
        # leaves a tool that differs from the frozen one in exactly one layer.
        frozen_rules = [r for r in frozen_rules if r.name.startswith("generic_")]
        args.no_llm = True                     # the ablation is a local question
    att_build, build_usd = _build_cost(frozen_path)
    rules_build = [r.name for r in frozen_rules
                   if not r.name.startswith("generic_")]

    index = ReferenceIndex(correct)
    budget = SearchBudget(**({"max_nodes": args.max_nodes} if args.max_nodes else {}))

    # A patch as large as the program it repairs is a rewrite, not a repair.
    gate = None if args.no_llm else RPS_GATE
    replay = _replayed(args.problem, args.model) if args.replay_fallback else None

    rows_l: list[dict] = []
    rows_lf: list[dict] = []
    gated = gate_won = 0

    for f in files:
        src = f.read_text()
        t0 = time.time()
        fz = local_repair(src, prob, frozen_rules, index, budget, args.granularity)
        t_frozen = time.time() - t0

        if fz.repaired:
            pr = rps(src, fz.patch)
            row = event_row(f.stem, model_label, fz.source, True, fz.patch,
                            pr, att_cpu=t_frozen, rules_l=fz.rules)
            rows_l.append(row)                 # TEMPA_L takes what passes
            if gate is None or pr <= gate:
                rows_lf.append(dict(row))
                continue
            # Gate: this patch is an outlier for this assignment, so spend the
            # call. Keep whichever patch is smaller, so escalating can lose
            # money but never coverage or patch size.
            gated += 1
            fb = (replay(f.stem) if replay
                  else fallback_repair(src, prob, correct, model=args.model))
            fb_pr = rps(src, fb.patch) if fb.repaired else None
            better = fb.repaired and fb_pr < pr
            if better:
                gate_won += 1
            rows_lf.append(event_row(
                f.stem, model_label, "llm" if better else fz.source, True,
                fb.patch if better else fz.patch, fb_pr if better else pr,
                att_cpu=t_frozen, att_api=fb.seconds, in_tok=fb.in_tokens,
                out_tok=fb.out_tokens, api_usd=fb.usd,
                rules_l=[] if better else fz.rules))
            continue

        rows_l.append(event_row(f.stem, model_label, "none", False,
                                att_cpu=t_frozen))
        if args.no_llm:                        # TEMPA_L-only mode (dry runs)
            rows_lf.append(event_row(f.stem, model_label, "none", False,
                                     att_cpu=t_frozen))
            continue

        fb = (replay(f.stem) if replay
              else fallback_repair(src, prob, correct, model=args.model))
        rows_lf.append(event_row(f.stem, model_label,
                                 "llm" if fb.repaired else "none", fb.repaired,
                                 fb.patch, rps(src, fb.patch) if fb.repaired else None,
                                 att_cpu=t_frozen, att_api=fb.seconds,
                                 in_tok=fb.in_tokens, out_tok=fb.out_tokens,
                                 api_usd=fb.usd))

    if args.framework_only:
        write_events(args.ver, args.problem, "tempa_l_fw", rows_l)
    else:
        write_events(args.ver, args.problem, "tempa_l", rows_l)
        write_events(args.ver, args.problem, "tempa_lf", rows_lf)
    # Summarize the whole file, not just the rows this pass produced: a
    # --only-missing run touches a handful of submissions, but the arm's
    # reported result is the pool.
    # Only summarize what this pass actually wrote. Upserting another arm's
    # row from an empty list zeroes a completed measurement, which is exactly
    # what the ablation did to TEMPA_LF before this guard existed.
    written = ([("TEMPA_L_fw", "tempa_l_fw")] if args.framework_only
               else [("TEMPA_L", "tempa_l"), ("TEMPA_LF", "tempa_lf")])
    for approach, stem in written:
        rows = read_events(args.ver, args.problem, stem, model_label)
        upsert_summary(args.ver, args.problem,
                       summarize_events(approach, model_label, rows,
                                        att_build=att_build,
                                        build_usd=build_usd,
                                        rules_build=rules_build))

    def rr(rows):
        return 100 * sum(r["Fixed"] for r in rows) / max(1, len(rows))

    print(f"=== {args.problem} [{model_label}] {len(files)} programs ===")
    print(f"ATT_build={att_build}s  $Build={build_usd}")
    print("RPS gate: " + (f"tau={gate}, fired on {gated} "
                          f"({100*gated/max(1,len(rows_l)):.1f}%), "
                          f"smaller patch on {gate_won}"
                          if gate is not None else "off (--no-llm)"))
    shown = ([("TEMPA_L_fw", rows_l)] if args.framework_only
             else [("TEMPA_L", rows_l), ("TEMPA_LF", rows_lf)])
    for name, rows in shown:
        print(f"  {name:10s} RR={rr(rows):6.2f}%  n={len(rows)}")
    print(f"results -> results/{args.ver}/{args.problem}/")
    return 0
