"""`run.py cluster-once` — the amortization a builder is measured against.

Instead of synthesizing rules, query the model once per cluster of Select and
spread that answer to the cluster: for each cluster, the fallback query on its
representative (Select's medoid) is sent, and every member is repaired by
transplanting from the representative's repaired program when that passes,
else as TEMPA_L-Rules repairs it (always-on rules, then the class's pool);
whatever is left escalates on TEMPA_LF's gate. Every query is LLM_Direct's
logged one, judged as LLM_Direct is (T+ on R1-R5), so the arm costs no new call.

    python run.py cluster-once --problem P   # -> results/cluster_once/<pid>/tempa_lf.csv
"""
from __future__ import annotations

import argparse
from pathlib import Path

from src.core.cluster import cluster, cluster_docs, edit_script, pair_by_bfs
from src.core.reference_repair import ReferenceIndex, reference_repair
from src.experiments._common import ORDER, load_pool, load_problem
from src.experiments.compose import RPS_GATE
from src.experiments.results_io import event_row, read_events, write_events
from src.utils.metrics import rps

ROOT = Path(__file__).resolve().parents[2]
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def clusters(pid: str) -> dict[str, str]:
    """Each buggy program's cluster representative, as Select forms them."""
    names = sorted(p.stem for p in (ROOT / "benchmark" / pid / "buggy").glob("*.py"))
    buggy, correct = load_pool(pid, "buggy"), load_pool(pid, "correct")
    partner, _edit = pair_by_bfs(buggy, correct)
    docs = [edit_script(b, correct[int(partner[i])]) for i, b in enumerate(buggy)]
    cs, _ = (cluster_docs(docs, distance_threshold=None) if any(docs) else cluster(buggy))
    return {names[i]: names[c.medoid] for c in cs for i in c.members}


def run(pid: str) -> None:
    rep = clusters(pid)
    for m in MODELS:
        prob = load_problem(pid, amplified=m if pid in ORDER[:5] else None)
        direct = {str(r["Buggy"]): r for r in read_events("", pid, "direct_llm", m)}
        fw = {str(r["Buggy"]): r for r in read_events("", pid, "tempa_l_fw", m)}
        rows = []
        for b, r in sorted(rep.items()):
            src = (ROOT / "benchmark" / pid / "buggy" / f"{b}.py").read_text()
            seed = direct[r]
            spent = b == r                     # the representative's query is its own
            if b == r and seed["Fixed"]:
                rows.append(event_row(b, m, "llm", True, seed["Patch"], seed["RPS"],
                                      att_api=seed["ATT_api"], api_usd=seed["$API"]))
                continue
            local = None
            if seed["Fixed"] and b != r:       # spread the cluster's answer
                got = reference_repair(src, prob, ReferenceIndex([seed["Patch"]]))
                if got.repaired:
                    local = ("cluster", got.patch, rps(src, got.patch))
            if local is None and fw[b]["Fixed"]:
                local = (fw[b]["Source"], fw[b]["Patch"], fw[b]["RPS"])
            usd = seed["$API"] if spent else 0.0
            if local and local[2] <= RPS_GATE:
                rows.append(event_row(b, m, local[0], True, local[1], local[2], api_usd=usd))
                continue
            fb = direct[b]                     # escalate, as TEMPA_LF does
            usd = fb["$API"] if not spent else usd
            if fb["Fixed"] and (local is None or fb["RPS"] < local[2]):
                rows.append(event_row(b, m, "llm", True, fb["Patch"], fb["RPS"], api_usd=usd))
            elif local:
                rows.append(event_row(b, m, local[0], True, local[1], local[2], api_usd=usd))
            else:
                rows.append(event_row(b, m, "none", False, None, None, api_usd=usd))
        write_events("cluster_once", pid, "tempa_lf", rows)
        n = len(set(rep.values()))
        print(f"{pid} [{m}]: {n} clusters, RR {100 * sum(x['Fixed'] for x in rows) / len(rows):.2f}%, "
              f"${sum(float(x['$API']) for x in rows):.2f}", flush=True)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py cluster-once")
    ap.add_argument("--problem", choices=ORDER, required=True)
    run(ap.parse_args(argv).problem)
    return 0
