"""`run.py split-fallback` — the fallback query, issued with a split's own pool.

A tool of Section 5.5 is built from a class's first f% and repairs its last
quarter, so on escalation TEMPA_LF's query attaches the minimum-edit reference
program pi(b) from the correct programs that split holds, and shows the
failures on that split's acceptance suite. LLM_Direct's log answers queries made
with the whole class, so a split cannot take its answers from there. The thin
pools of Section 5.4 are the same with a pool of the split's first k correct
programs.

    python run.py split-fallback splits      # results/splits/<s>/<f>/<pid>/fallback_<m>.json
    python run.py split-fallback thin-pool   # results/thin_pool/fallback/<s>_<pid>_<m>_k<k>.json

A store maps a buggy program to its candidate and call accounting, as
LLM_Direct's does; a rerun queries only what a store lacks. `compose --splits`
and `thin-pool` then judge these answers against the split's suite.
"""
from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd

from src.core.fallback import fallback_repair
from src.experiments._common import IDS, ORDER, load_env
from src.experiments.compose import escalated
from src.experiments.results_io import read_events

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / "splits_work"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def _data(scheme: str, tag: str, pid: str, model: str) -> Path:
    return WORK / scheme / tag / (f"eval_amplified/{model}" if pid in ORDER[:5] else "eval") / pid


def _query(store: Path, stems: list[str], data: Path, pool: list[str], model: str) -> float:
    """Ask for every stem the store lacks; returns what this pass spent."""
    got = json.loads(store.read_text()) if store.exists() else {}
    todo = [s for s in stems if s not in got]
    prob = json.loads((data / "problem.json").read_text())

    def ask(s):
        try:
            fb = fallback_repair((data / "buggy" / f"{s}.py").read_text(), prob, pool, model=model)
        except Exception as e:                 # noqa: BLE001 - a failed call is a miss
            return s, {"candidate": None, "error": type(e).__name__}
        return s, {"candidate": fb.candidate, "in": fb.in_tokens, "out": fb.out_tokens,
                   "s": fb.seconds, "usd": fb.usd}
    spent = 0.0
    with ThreadPoolExecutor(8) as ex:
        for i, (s, c) in enumerate(ex.map(ask, todo), 1):
            got[s] = c
            spent += c.get("usd", 0.0)
            if i % 25 == 0 or i == len(todo):
                store.parent.mkdir(parents=True, exist_ok=True)
                store.write_text(json.dumps(got))
    return spent


def splits() -> float:
    spent = 0.0
    for f in sorted((ROOT / "results" / "splits").glob("s*/f*/*/tempa_l.csv")):
        scheme, tag, pid = f.parts[-4], f.parts[-3], f.parts[-2]
        ver = str(f.parent.parent.relative_to(ROOT / "results"))
        for m in MODELS:
            need = [str(r["Buggy"]) for r in escalated(read_events(ver, pid, "tempa_l", m))]
            data = _data(scheme, tag, pid, m)
            pool = [p.read_text() for p in sorted((data / "correct").glob("*.py"))]
            usd = _query(f.parent / f"fallback_{m}.json", need, data, pool, m)
            spent += usd
            print(f"{scheme}/{tag} {pid} [{m}]: {len(need)} escalations, ${usd:.4f}", flush=True)
    return spent


def thin_pool() -> float:
    spent, pids = 0.0, {v: k for k, v in IDS.items()}
    manifest = json.loads((WORK / "manifest.json").read_text())
    for f in sorted((ROOT / "results" / "thin_pool").glob("s*_*.csv")):
        d = pd.read_csv(f, keep_default_na=False)
        d = d[d.esc.astype(str) == "True"]
        for (scheme, label, m, k), g in d.groupby(["scheme", "pid", "model", "k"]):
            pid = pids[label]
            data = _data(scheme, "f10", pid, m)
            order = manifest[scheme][pid]["train"]["10"]["correct"][:int(k)]
            pool = [(data / "correct" / f"{s}.py").read_text() for s in order]
            store = ROOT / "results" / "thin_pool" / "fallback" / f"{scheme}_{pid}_{m}_k{k}.json"
            usd = _query(store, sorted(set(g.buggy.astype(str))), data, pool, m)
            spent += usd
            print(f"thin {scheme} {pid} [{m}] k={k}: {g.buggy.nunique()} escalations, ${usd:.4f}",
                  flush=True)
    return spent


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py split-fallback")
    ap.add_argument("which", choices=["splits", "thin-pool"])
    args = ap.parse_args(argv)
    load_env()
    spent = splits() if args.which == "splits" else thin_pool()
    print(f"spent ${spent:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
