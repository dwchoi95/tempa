"""Unified results storage — the agreed CSV format, one definition for every
approach (Refactory, PyDex, PyDex_PC, LLM_Direct, TEMPA_L, TEMPA_LF).

Layout:
    results/<ver>/<p_id>/<approach>.csv   one row per truly-buggy submission
    results/<ver>/<p_id>/summary.csv      one row per (Approach, Model)
    results/<ver>/overall.csv             N-weighted micro-averages + totals

Event columns (per submission):
    Buggy, Model, Source, Patch, Fixed, RPS, ATT_all, ATT_cpu, ATT_api,
    InT, OuT, $API, Rules_L, Rules_SL
    - Source: TEMPA rules|reference|llm|sl_rules|none; PyDex llm|none;
      Refactory reference|none.
    - Patch stored only when Fixed; list columns are JSON strings.

Summary columns:
    Approach, Model, N, RR, RPS, ATT_all, ATT_cpu, ATT_api, ATT_build,
    InT, OuT, $API, $Build, Rules_build, Rules_add, Rules_used
    - Rules_used is a JSON dict {rule_name: fire_count}.

Overall columns:
    Approach, Model, RR, RPS, ATT_all, ATT_cpu, ATT_api, ATT_build,
    InT, OuT, $API, $Build
    - RR/RPS/ATT are N-weighted micro-averages over problems (RPS weighted by
      repaired count); ATT_build is the per-problem mean (consistent with the
      other ATT columns); InT/OuT/$API/$Build are totals.
"""
from __future__ import annotations

import json
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[2]

EVENT_COLS = ["Buggy", "Model", "Source", "Patch", "Fixed", "RPS",
              "ATT_all", "ATT_cpu", "ATT_api", "InT", "OuT", "$API",
              "Rules_L", "Rules_SL"]
SUMMARY_COLS = ["Approach", "Model", "N", "RR", "RPS",
                "ATT_all", "ATT_cpu", "ATT_api", "ATT_build",
                "InT", "OuT", "$API", "$Build",
                "Rules_build", "Rules_add", "Rules_used"]
OVERALL_COLS = ["Approach", "Model", "RR", "RPS",
                "ATT_all", "ATT_cpu", "ATT_api", "ATT_build",
                "InT", "OuT", "$API", "$Build"]


def jlist(x) -> str:
    if isinstance(x, str):   # already encoded, as read back from a results CSV
        x = json.loads(x or "[]")
    return json.dumps(list(x))


def jdict(x) -> str:
    return json.dumps(dict(x))


def event_row(buggy: str, model: str, source: str, fixed: bool,
              patch: str | None = None, rps: float | None = None,
              att_cpu: float = 0.0, att_api: float = 0.0,
              in_tok: int = 0, out_tok: int = 0, api_usd: float = 0.0,
              rules_l=(), rules_sl=()) -> dict:
    return {"Buggy": buggy, "Model": model, "Source": source,
            "Patch": (patch or "") if fixed else "",
            "Fixed": bool(fixed),
            "RPS": round(rps, 4) if (fixed and rps is not None) else None,
            "ATT_all": round(att_cpu + att_api, 4),
            "ATT_cpu": round(att_cpu, 4), "ATT_api": round(att_api, 4),
            "InT": int(in_tok), "OuT": int(out_tok),
            "$API": round(api_usd, 6),
            "Rules_L": jlist(rules_l), "Rules_SL": jlist(rules_sl)}


def write_events(ver: str, pid: str, approach_file: str, rows: list[dict]) -> Path:
    """Upsert this run's rows into the arm's event file, keyed by (Buggy, Model).

    The file carries a Model column because one arm is evaluated under several
    models; a plain overwrite meant the second model erased the first, leaving
    only the last-run model's per-submission rows on disk while the summary
    still listed both. Rows for other models, and for submissions this run did
    not touch (a --subset pass), are preserved.
    """
    d = ROOT / "results" / ver / pid
    d.mkdir(parents=True, exist_ok=True)
    path = d / f"{approach_file}.csv"
    fresh = pd.DataFrame(rows, columns=EVENT_COLS)
    if path.exists() and len(fresh):
        prior = pd.read_csv(path)
        # Buggy ids read back as ints on the numeric Codeforces corpus, so key
        # on their string form to compare like with like.
        def key(df):
            return df.Buggy.astype(str) + "\x00" + df.Model.astype(str)
        prior = prior[~key(prior).isin(set(key(fresh)))]
        fresh = pd.concat([prior, fresh], ignore_index=True)[EVENT_COLS]
    fresh.to_csv(path, index=False)
    return path


def read_events(ver: str, pid: str, approach_file: str,
                model: str | None = None) -> list[dict]:
    """This arm's rows as already written, optionally for one model only.

    A partial pass must summarize the whole file rather than the handful of
    rows it happened to produce, or the summary silently narrows to that
    handful while the event file still holds everything.
    """
    path = ROOT / "results" / ver / pid / f"{approach_file}.csv"
    if not path.exists():
        return []
    df = pd.read_csv(path)
    if model is not None:
        df = df[df.Model.astype(str) == str(model)]
    return df.to_dict("records")


def summarize_events(approach: str, model: str, rows: list[dict],
                     att_build: float = 0.0, build_usd: float = 0.0,
                     rules_build=(), rules_add=()) -> dict:
    n = len(rows)
    fixed = [r for r in rows if r["Fixed"]]
    used: dict[str, int] = {}
    for r in rows:
        for name in json.loads(r["Rules_L"]):
            used[name] = used.get(name, 0) + 1
    rps_vals = [r["RPS"] for r in fixed if r["RPS"] is not None]
    return {"Approach": approach, "Model": model, "N": n,
            "RR": round(len(fixed) / max(1, n), 4),
            "RPS": round(sum(rps_vals) / max(1, len(rps_vals)), 4),
            "ATT_all": round(sum(r["ATT_all"] for r in rows) / max(1, n), 4),
            "ATT_cpu": round(sum(r["ATT_cpu"] for r in rows) / max(1, n), 4),
            "ATT_api": round(sum(r["ATT_api"] for r in rows) / max(1, n), 4),
            "ATT_build": round(att_build, 2),
            "InT": int(sum(r["InT"] for r in rows)),
            "OuT": int(sum(r["OuT"] for r in rows)),
            "$API": round(sum(r["$API"] for r in rows), 6),
            "$Build": round(build_usd, 6),
            "Rules_build": jlist(rules_build), "Rules_add": jlist(rules_add),
            "Rules_used": jdict(used)}


def upsert_summary(ver: str, pid: str, row: dict) -> Path:
    d = ROOT / "results" / ver / pid
    d.mkdir(parents=True, exist_ok=True)
    path = d / "summary.csv"
    if path.exists():
        df = pd.read_csv(path)
        mask = (df["Approach"] == row["Approach"]) & (df["Model"] == row["Model"])
        df = df[~mask]
    else:
        df = pd.DataFrame(columns=SUMMARY_COLS)
    df = pd.concat([df, pd.DataFrame([row], columns=SUMMARY_COLS)],
                   ignore_index=True)
    df.to_csv(path, index=False)
    return path


def build_overall(ver: str) -> Path:
    base = ROOT / "results" / ver
    acc: dict[tuple, dict] = {}
    for summ in sorted(base.glob("*/summary.csv")):
        df = pd.read_csv(summ, keep_default_na=False)
        for _, r in df.iterrows():
            key = (r["Approach"], r["Model"])
            a = acc.setdefault(key, {"n": 0, "rep": 0, "rps_sum": 0.0,
                                     "all": 0.0, "cpu": 0.0, "api": 0.0,
                                     "build_t": 0.0, "probs": 0, "InT": 0,
                                     "OuT": 0, "usd": 0.0, "busd": 0.0})
            n, rr = int(r["N"]), float(r["RR"])
            rep = round(rr * n)
            a["n"] += n
            a["rep"] += rep
            a["rps_sum"] += float(r["RPS"]) * rep
            a["all"] += float(r["ATT_all"]) * n
            a["cpu"] += float(r["ATT_cpu"]) * n
            a["api"] += float(r["ATT_api"]) * n
            a["build_t"] += float(r["ATT_build"])
            a["probs"] += 1
            a["InT"] += int(r["InT"])
            a["OuT"] += int(r["OuT"])
            a["usd"] += float(r["$API"])
            a["busd"] += float(r["$Build"])
    rows = []
    for (app, model), a in sorted(acc.items()):
        n, rep = max(1, a["n"]), a["rep"]
        rows.append({"Approach": app, "Model": model,
                     "RR": round(rep / n, 4),
                     "RPS": round(a["rps_sum"] / max(1, rep), 4),
                     "ATT_all": round(a["all"] / n, 4),
                     "ATT_cpu": round(a["cpu"] / n, 4),
                     "ATT_api": round(a["api"] / n, 4),
                     "ATT_build": round(a["build_t"] / max(1, a["probs"]), 2),
                     "InT": a["InT"], "OuT": a["OuT"],
                     "$API": round(a["usd"], 6),
                     "$Build": round(a["busd"], 6)})
    path = base / "overall.csv"
    pd.DataFrame(rows, columns=OVERALL_COLS).to_csv(path, index=False)
    return path
