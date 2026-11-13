"""Shared helpers for the experiment drivers (data loading, .env, arg parsing)."""
from __future__ import annotations

import json
import os
from pathlib import Path


# The 11 assignments in the order the paper lists them, and the short ids it
# uses: R for the CS1 corpus, C for Codeforces in rating order.
ORDER = ["refactory_q1", "refactory_q2", "refactory_q3", "refactory_q4",
         "refactory_q5", "cf_110A", "cf_131A", "cf_1011B", "cf_125A",
         "cf_11B", "cf_10C"]
IDS = {p: (f"R{i+1}" if i < 5 else f"C{i-4}") for i, p in enumerate(ORDER)}


def load_env(path: str = ".env") -> None:
    """Load KEY=VALUE lines from .env into os.environ (llm.py reads os.environ)."""
    p = Path(path)
    if not p.exists():
        return
    for line in p.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


def load_problem(pid: str, root: str = "benchmark", amplified: str | None = None) -> dict:
    """<root>/<pid>/problem.json: the description and the instructor's tests T.

    With ``amplified=<model>``, the tests are T+ = T plus the suite that
    builder's generator produced (benchmark/<pid>/amplified/<model>/tests.json,
    R1-R5); where none exists, T+ = T. ``n_instructor`` records that T is the
    first that many tests, which the rule search orders and prunes by.
    """
    prob = json.loads((Path(root) / pid / "problem.json").read_text())
    amp = Path(root) / pid / "amplified" / str(amplified) / "tests.json"
    if amplified and amp.exists():
        prob = dict(prob, tests=prob["tests"] + json.loads(amp.read_text()),
                    n_instructor=len(prob["tests"]))
    return prob


def load_pool(pid: str, kind: str, root: str = "benchmark") -> list[str]:
    """Read every .py under benchmark/<pid>/<kind> (kind = 'buggy' | 'correct')."""
    d = Path(root) / pid / kind
    return [f.read_text() for f in sorted(d.glob("*.py"))]


def tool_path(pid: str, model: str, root: str = "tools") -> Path:
    """tools/<pid>/<model>/fixer.rules — the tool directory is the model name."""
    return Path(root) / pid / model / "fixer.rules"
