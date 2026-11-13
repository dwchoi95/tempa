#!/usr/bin/env python3
"""Import selected Codeforces problems into the unified `data/<pid>/` schema.

Sources (HuggingFace, queried through the datasets-server so nothing large is
downloaded):
  * open-r1/codeforces              (config `verifiable`) - statements + official tests
  * open-r1/codeforces-submissions  (config `default`)    - real Python 3 submissions

Selection criteria applied upstream (see PLAN.md): verifiable subset, Python 3,
at least one WRONG_ANSWER and one OK submission, `official_tests_complete` (no
truncated test case), no `generated_checker` (single valid output), and at most
30 official tests.

Programs read stdin and print stdout, so imported problems use `mode: "stdio"`.

Layout produced:
    data/cf_<contest><index>/problem.json     statement, official tests, time limit
    data/cf_<contest><index>/buggy/<sid>.py   WRONG_ANSWER submissions
    data/cf_<contest><index>/correct/<sid>.py OK submissions (reference pool)

Usage:  python data/_import/codeforces.py --problems 1011/A 104/A ...
"""
from __future__ import annotations

import argparse
import json
import re
import time
import urllib.parse
import urllib.request
from pathlib import Path

SERVER = "https://datasets-server.huggingface.co"
PAGE = 100


def _get(endpoint: str, params: dict, retries: int = 6) -> dict:
    url = f"{SERVER}/{endpoint}?{urllib.parse.urlencode(params)}"
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(url, timeout=180) as r:
                return json.load(r)
        except Exception:
            time.sleep(3 + 3 * attempt)
    raise RuntimeError(f"failed after {retries} attempts: {endpoint} {params}")


def fetch_problem(pid: str) -> dict:
    d = _get("filter", {"dataset": "open-r1/codeforces", "config": "verifiable",
                        "split": "train", "where": f"\"id\"='{pid}'", "limit": 1})
    rows = d.get("rows", [])
    if not rows:  # a few selected problems live in the test split
        d = _get("filter", {"dataset": "open-r1/codeforces", "config": "verifiable",
                            "split": "test", "where": f"\"id\"='{pid}'", "limit": 1})
        rows = d.get("rows", [])
    if not rows:
        raise RuntimeError(f"problem {pid} not found")
    return rows[0]["row"]


def fetch_submissions(pid: str, verdict: str) -> list[dict]:
    out, offset = [], 0
    where = (f"\"problem_id\"='{pid}' AND \"programmingLanguage\"='Python 3' "
             f"AND \"verdict\"='{verdict}'")
    while True:
        d = _get("filter", {"dataset": "open-r1/codeforces-submissions",
                            "config": "default", "split": "train", "where": where,
                            "offset": offset, "length": PAGE})
        rows = [r["row"] for r in d.get("rows", [])]
        out.extend(rows)
        total = d.get("num_rows_total", len(out))
        offset += PAGE
        if offset >= total or not rows:
            return out


def statement(row: dict) -> str:
    parts = [f"# {row.get('title', '').strip()}", (row.get("description") or "").strip()]
    for label, key in (("Input", "input_format"), ("Output", "output_format"),
                       ("Note", "note")):
        val = (row.get(key) or "").strip()
        if val:
            parts.append(f"## {label}\n{val}")
    return "\n\n".join(p for p in parts if p.strip())


def _clean(code: str) -> str:
    return re.sub(r"\r\n?", "\n", code or "")


def slug(pid: str) -> str:
    return "cf_" + pid.replace("/", "")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problems", nargs="+", required=True,
                    help="Codeforces problem ids, e.g. 1011/A")
    ap.add_argument("--out", default="data", type=Path)
    args = ap.parse_args()

    total_bug = total_ok = 0
    for pid in args.problems:
        row = fetch_problem(pid)
        tests = [{"stdin": _clean(t["input"]), "expected": _clean(t["output"])}
                 for t in (row.get("official_tests") or [])]
        if not tests:
            print(f"  !! {pid}: no official tests, skipped")
            continue

        pdir = args.out / slug(pid)
        (pdir / "buggy").mkdir(parents=True, exist_ok=True)
        (pdir / "correct").mkdir(parents=True, exist_ok=True)

        wa = fetch_submissions(pid, "WRONG_ANSWER")
        ok = fetch_submissions(pid, "OK")
        for sub in wa:
            (pdir / "buggy" / f"{sub['submission_id']}.py").write_text(_clean(sub["source"]))
        for sub in ok:
            (pdir / "correct" / f"{sub['submission_id']}.py").write_text(_clean(sub["source"]))

        mode = "file" if row.get("input_mode") == "file" else "stdio"
        (pdir / "problem.json").write_text(json.dumps({
            "pid": slug(pid), "source": "codeforces", "cf_id": pid, "mode": mode,
            "rating": row.get("rating"), "time_limit": row.get("time_limit"),
            "official_tests_complete": bool(row.get("official_tests_complete")),
            "description": statement(row), "tests": tests,
        }, indent=1))
        total_bug += len(wa)
        total_ok += len(ok)
        print(f"  {slug(pid)}: buggy={len(wa)} correct={len(ok)} tests={len(tests)} "
              f"rating={row.get('rating')}")

    print(f"imported {total_bug} buggy + {total_ok} correct programs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
