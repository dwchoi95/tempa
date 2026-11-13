"""Collect the Refactory tool's CSVs into the agreed unified format:

    results/<ver>/<p_id>/refactory.csv   one row per buggy submission
    results/<ver>/<p_id>/summary.csv     upserted (Approach=Refactory, Model=none)

Source is ``reference`` on success (Refactory's mechanism *is* reference
reuse) and ``none`` otherwise; submissions the adapter could not export are
rows with Fixed=False (shared full denominator). Refactory has no LLM columns
(ATT_api/InT/OuT/$API/$Build = 0) and no rules.

Every submission the corpus labels buggy is a repair target for every arm, so
the denominator is the pool as published and is identical across arms.

RPS is recomputed from the returned patch rather than read from their CSV.
Refactory rewrites each program into ``def main(): try: <body> except _Exit:
pass`` and reformats it, and reports RPS between the *wrapped* buggy program
and the *wrapped* repair. That is a fair measure of its own edit, but not the
same quantity we compute for the other arms, and the wrapper inflates the
denominator, so the reported value runs low: on cf_125A theirs averages 0.523
where the same patches measured on the same footing as every other arm average
0.606. We strip the scaffold and measure against the student's original
program, which is what TEMPA and PyDex are measured against.

Usage: python3 -m src.experiments.refactory_results cf_125A [cf_110A ...]
"""
from __future__ import annotations

import argparse
import ast
from pathlib import Path

import pandas as pd

from src.utils.metrics import rps as compute_rps
from src.experiments.results_io import (build_overall, event_row,
                                        summarize_events, upsert_summary,
                                        write_events)

ROOT = Path(__file__).resolve().parents[2]


def unwrap(src: str) -> str:
    """Undo Refactory's ``def main(): try: ... except _Exit: pass`` scaffold.

    Reformatting does not matter -- RPS is computed over ASTs -- but the
    wrapper does: it adds nodes to both sides, and the extra nodes in the
    denominator make every patch look smaller than it is.
    """
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return src
    fn = next((n for n in tree.body
               if isinstance(n, ast.FunctionDef) and n.name == "main"), None)
    if fn is None:
        return src
    inner = fn.body
    if len(inner) == 1 and isinstance(inner[0], ast.Try):
        inner = inner[0].body

    def is_guard(n) -> bool:                 # the `if __name__ == ...: main()`
        return isinstance(n, ast.If) and "__name__" in ast.dump(n.test)

    def is_call(n) -> bool:                  # a bare `main()` at module level
        return (isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
                and getattr(n.value.func, "id", "") == "main")

    keep = [n for n in tree.body
            if n is not fn and not is_guard(n) and not is_call(n)]
    try:
        return ast.unparse(ast.Module(body=keep + inner, type_ignores=[]))
    except Exception:                        # noqa: BLE001 - keep the original
        return src


def source_csv(pid: str) -> Path:
    """Where this problem's Refactory output lives.

    Codeforces problems were run by us into ``data_cf``. The five Refactory
    assignments ship the authors' own run of their tool on their own data
    (``data/question_N``), which is the tool at the configuration they report;
    re-running it could only reproduce that less faithfully. Either way the
    patch is re-measured here on our footing, which is the whole point.
    """
    if pid.startswith("refactory_q"):
        return (ROOT / "baselines" / "refactory" / "data"
                / f"question_{pid.rsplit('_q', 1)[1]}" / "refactory_online.csv")
    return ROOT / "baselines" / "refactory" / "data_cf" / pid / "refactory_online.csv"


def collect(pid: str, ver: str = "") -> dict:
    csv = source_csv(pid)
    df = pd.read_csv(csv, keep_default_na=False)
    by_name = {r["File Name"]: r for _, r in df.iterrows()}
    buggy_dir = ROOT / "benchmark" / pid / "buggy"
    all_buggy = sorted(p.name for p in buggy_dir.glob("*.py"))

    rows = []
    for name in all_buggy:
        stem = name[:-3]
        r = by_name.get(name)
        if r is None:                          # adapter could not export it
            rows.append(event_row(stem, "none", "none", False))
            continue
        ok = str(r["Status"]).startswith("success")
        patch = str(r.get("Repair", "")) if ok else None

        def num(v):                        # their CSV writes 'N/A' on some fails
            try:
                return float(v)
            except (TypeError, ValueError):
                return None

        rps = None
        if ok and patch:
            try:
                rps = compute_rps((buggy_dir / name).read_text(), unwrap(patch))
            except Exception:                # noqa: BLE001 - unparseable patch
                rps = num(r["RPS"])          # fall back to their own figure
        rows.append(event_row(stem, "none", "reference" if ok else "none", ok,
                              patch, rps, att_cpu=num(r["Total Time"]) or 0.0))

    write_events(ver, pid, "refactory", rows)
    summ = summarize_events("Refactory", "none", rows)
    upsert_summary(ver, pid, summ)
    print(f"{pid}: {len(rows)} submissions, "
          f"RR={100*summ['RR']:.2f}% RPS={summ['RPS']:.4f}")
    return summ


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("pids", nargs="+")
    ap.add_argument("--ver", default="",
                    help="optional subdirectory under results/; empty means "
                         "results/ itself, which is where the campaign wrote")
    args = ap.parse_args(argv)
    for pid in args.pids:
        try:
            s = collect(pid, args.ver)
        except Exception as e:                     # noqa: BLE001
            print(f"[{pid}] collect FAILED: {type(e).__name__}: {e}")
            continue
        print(f"[{pid}] Refactory RR={s['RR']} RPS={s['RPS']} "
              f"ATT_cpu={s['ATT_cpu']}s -> results/{args.ver}/{pid}/")
    build_overall(args.ver)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
