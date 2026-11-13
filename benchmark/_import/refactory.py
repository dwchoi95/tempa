#!/usr/bin/env python3
"""Import the Refactory (ASE'19) corpus into the unified `data/<pid>/` schema.

Source: the Refactory replication package (githubhuyang/refactory), cloned into
baselines/refactory/ —
real Python submissions by 361 NUS students to five CS1 assignments. Programs
define functions that the tests call directly, so imported problems use
`mode: "call"`.

Test cases live in `ans/input_NNN.txt` / `ans/output_NNN.txt`, where the input
file holds a call expression such as `unique_day('1', [...])`. Each test records
its own callee, because one assignment requires three separate functions.

Layout produced:

    data/<pid>/problem.json     description, entry, tests, mode
    data/<pid>/buggy/<n>.py     wrong submissions
    data/<pid>/correct/<n>.py   correct submissions (reference pool)
    data/<pid>/reference.py     the instructor's reference solution

Reference *selection* happens at split time; the whole correct pool is imported.

Usage:  python data/_import/refactory.py [--src baselines/refactory/data] [--out data]
"""
from __future__ import annotations

import argparse
import ast
import json
import re
from pathlib import Path

CALL_RE = re.compile(r"^\s*(\w+)\s*\((.*)\)\s*$", re.S)


def entry_of(reference_src: str) -> str:
    """Name of the last top-level function in the reference solution."""
    tree = ast.parse(reference_src)
    names = [n.name for n in tree.body if isinstance(n, ast.FunctionDef)]
    if not names:
        raise ValueError("reference defines no function")
    return names[-1]


def parse_tests(ansdir: Path, entry: str) -> list[dict]:
    tests = []
    for inp in sorted(ansdir.glob("input_*.txt")):
        out = ansdir / inp.name.replace("input_", "output_")
        if not out.exists():
            continue
        raw_in, raw_out = inp.read_text().strip(), out.read_text().strip()
        m = CALL_RE.match(raw_in)
        callee, call = (m.group(1), m.group(2)) if m else (entry, raw_in)
        try:
            args = list(ast.literal_eval(f"({call},)")) if call else []
            expected = ast.literal_eval(raw_out)
        except (ValueError, SyntaxError):
            continue
        test = {"args": args, "expected": expected}
        if callee != entry:
            test["entry"] = callee
        tests.append(test)
    return tests


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="baselines/refactory/data", type=Path)
    ap.add_argument("--out", default="data", type=Path)
    args = ap.parse_args()

    total_bugs = 0
    for qdir in sorted(args.src.glob("question_*")):
        pid = "refactory_" + qdir.name.replace("question_", "q")
        code = qdir / "code"
        reference = (code / "reference" / "reference.py").read_text()
        entry = entry_of(reference)
        tests = parse_tests(qdir / "ans", entry)
        if not tests:
            print(f"  !! {pid}: no parsable tests, skipped")
            continue

        pdir = args.out / pid
        (pdir / "buggy").mkdir(parents=True, exist_ok=True)
        (pdir / "correct").mkdir(parents=True, exist_ok=True)
        (pdir / "reference.py").write_text(reference)

        n_bug = 0
        for f in sorted((code / "wrong").glob("*.py")):
            (pdir / "buggy" / f.name).write_text(f.read_text())
            n_bug += 1
        n_ok = 0
        for f in sorted((code / "correct").glob("*.py")):
            (pdir / "correct" / f.name).write_text(f.read_text())
            n_ok += 1

        desc_file = qdir / "description.txt"
        description = desc_file.read_text() if desc_file.exists() else pid
        (pdir / "problem.json").write_text(json.dumps({
            "pid": pid, "source": "refactory", "mode": "call",
            "entry": entry, "description": description, "tests": tests,
        }, indent=1))
        total_bugs += n_bug
        callees = sorted({t.get("entry", entry) for t in tests})
        print(f"  {pid}: entry={entry} callees={callees} tests={len(tests)} "
              f"buggy={n_bug} correct={n_ok}")

    print(f"imported {total_bugs} buggy programs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
