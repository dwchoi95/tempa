"""`run.py compose` — TEMPA_LF from the frozen tool's run and the logged query.

TEMPA_LF escalates a program when the frozen tool abstains or returns a patch
at least as large as the program (RPS > RPS_GATE), sends the single query
LLM(d, T, b, pi(b)), and keeps the smaller passing patch. LLM_Direct issued
exactly that query, under the same acceptance, for every buggy program, so
TEMPA_LF is composed from tempa_l.csv and direct_llm.csv instead of querying
again. The two arms then differ in the architecture alone, with the model's
answers held fixed.

    results/<pid>/tempa_lf.csv                    accepting T+ (T on C1-C6)
    results/<pid>/no_amplification/tempa_lf.csv   accepting T (R1-R5)
    and the TEMPA_LF rows of the matching summary.csv

Build cost and build time are the tool's, copied from the TEMPA_L summary row.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import pandas as pd

from src.experiments._common import ORDER
from src.experiments.results_io import (event_row, read_events, summarize_events,
                                        upsert_summary, write_events)

RPS_GATE = 1.0                                     # compare.py
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def compose(local: list[dict], direct: list[dict]) -> list[dict]:
    by = {str(r["Buggy"]): r for r in direct}
    out = []
    for lo in local:
        if lo["Fixed"] and lo["RPS"] is not None and lo["RPS"] <= RPS_GATE:
            out.append(dict(lo))
            continue
        fb = by[str(lo["Buggy"])]
        better = fb["Fixed"] and (not lo["Fixed"] or fb["RPS"] < lo["RPS"])
        keep = fb if better else lo
        out.append(event_row(
            str(lo["Buggy"]), lo["Model"], "llm" if better else lo["Source"],
            bool(keep["Fixed"]), keep["Patch"] if keep["Fixed"] else None,
            keep["RPS"] if keep["Fixed"] else None,
            att_cpu=lo["ATT_cpu"], att_api=fb["ATT_api"], in_tok=fb["InT"],
            out_tok=fb["OuT"], api_usd=fb["$API"],
            rules_l=[] if better else lo["Rules_L"]))
    return out


def run(pid: str, ver: str) -> None:
    for m in MODELS:
        local = read_events(ver, pid, "tempa_l", m)
        direct = read_events(ver, pid, "direct_llm", m)
        if not local or not direct:
            continue
        rows = compose(local, direct)
        write_events(ver, pid, "tempa_lf", rows)
        s = pd.read_csv(Path("results") / ver / pid / "summary.csv", keep_default_na=False)
        c = s[(s.Approach == "TEMPA_L") & (s.Model == m)].iloc[0]
        upsert_summary(ver, pid, summarize_events(
            "TEMPA_LF", m, read_events(ver, pid, "tempa_lf", m),
            att_build=float(c["ATT_build"]), build_usd=float(c["$Build"]),
            rules_build=json.loads(c["Rules_build"] or "[]")))
        fixed = sum(r["Fixed"] for r in rows)
        print(f"{pid} [{m}] {ver or '.'}: TEMPA_LF {100 * fixed / len(rows):.2f}%")


def judged_direct(rows: list[dict], pid: str, model: str, prob: dict,
                  buggy_dir: Path, store: Path | None = None) -> list[dict]:
    """The logged answer for each program of rows, judged against prob, as event
    rows: for a run whose acceptance suite is not the campaign's. store holds the
    answers to the run's own queries (split-fallback); LLM_Direct's log otherwise."""
    from concurrent.futures import ThreadPoolExecutor
    from src.runner.testing import run_tests
    from src.utils.metrics import rps
    cands = json.loads((store or Path(f"results/{pid}/direct_llm_{model}.json")).read_text())

    def judge(r):
        c = cands[str(r["Buggy"])]
        code = c.get("candidate") or ""
        ok = bool(code) and run_tests(code, prob).all_pass
        src = (buggy_dir / f"{r['Buggy']}.py").read_text()
        return event_row(str(r["Buggy"]), model, "llm" if ok else "none", ok,
                         code if ok else None, rps(src, code) if ok else None,
                         att_api=c.get("s", 0.0), in_tok=c.get("in", 0),
                         out_tok=c.get("out", 0), api_usd=c.get("usd", 0.0))
    with ThreadPoolExecutor(8) as ex:
        return list(ex.map(judge, rows))


def escalated(local: list[dict]) -> list[dict]:
    """The programs the gate sends to the fallback."""
    return [r for r in local if not (r["Fixed"] and r["RPS"] is not None
                                     and r["RPS"] <= RPS_GATE)]


def splits(root: str = "results/splits") -> None:
    """The same composition for the class splits of Section 5.5, whose acceptance
    suite is each split's own: LLM_Direct's kept answer for a program is judged
    against that split's tests before the gate compares it with the tool's."""
    for d in sorted(Path(root).glob("s*/*/*/tempa_l.csv")):
        scheme, tag, pid = d.parts[-4], d.parts[-3], d.parts[-2]
        ver = str(d.parent.parent.relative_to("results"))
        for m in MODELS:
            local = read_events(ver, pid, "tempa_l", m)
            if not local:
                continue
            data = (Path("splits_work") / scheme / tag /
                    ("eval_amplified/" + m if pid in ORDER[:5] else "eval") / pid)
            prob = json.loads((data / "problem.json").read_text())
            need = escalated(local)
            own = d.parent / f"fallback_{m}.json"     # queried with this split's pool
            direct = judged_direct(need, pid, m, prob, data / "buggy",
                                   own if own.exists() else None)
            write_events(ver, pid, "tempa_lf", compose(local, direct + [
                r for r in local if r not in need]))
        print(f"{ver}/{pid}: composed")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py compose")
    ap.add_argument("--splits", default="",
                    help="compose the class splits under this results root instead")
    args = ap.parse_args(argv)
    if args.splits:
        splits(args.splits)
        return 0
    for pid in ORDER:
        run(pid, "")
        if pid in ORDER[:5]:                       # R1-R5 accepting T alone
            run(f"{pid}/no_amplification", "")
    return 0
