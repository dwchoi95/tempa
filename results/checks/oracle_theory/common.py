"""Shared by certified.py and a4_pool.py: a fresh large sample from D, labelled
exactly as Amplify labels (augment.amplified_tests / augment.heldout), and a
chunked suite runner that keeps per-input verdicts. No LLM is called.

A sample is a list of draws (with repeats, in draw order) over distinct inputs;
each distinct input carries ref_ok (the reference returns), agree (>= 90% of the
41 voters give one non-error output) and its label. D = draws outside T (outside
T+ for the hand-written generator) with ref_ok and agree.
"""
from __future__ import annotations

import json
import random
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from src.experiments._common import load_problem  # noqa: E402
from src.experiments.augment import (AGREE, BENCH, N_VOTERS, _draw, _gen, _key,  # noqa: E402
                                     _outputs, _typed, held_keys, tplus_keys)
from src.runner.testing import run_tests  # noqa: E402

OUT = Path(__file__).resolve().parent
CACHE = OUT / "cache"
CS1 = [f"refactory_q{i}" for i in range(1, 6)]
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
SHORT = {"claude-sonnet-5": "cs", "gpt-5.4-mini": "gm", "heldout": "held-out gen"}
N_DRAWS = 20_000
CHUNK = 1000


def outputs(src: str, problem: dict, tests: list[dict]) -> list[str]:
    """augment._outputs in chunks, so one slow input cannot time out the lot."""
    return [o for i in range(0, len(tests), CHUNK)
            for o in _outputs(src, problem, tests[i:i + CHUNK])]


def label(pid: str, cands: list[dict], voter_seed: int) -> list[tuple[bool, object]]:
    """(agree, label) per candidate: augment._vote's voters and rule, no N_KEEP cap."""
    problem = load_problem(pid, str(BENCH))
    pool = sorted((BENCH / pid / "correct").glob("*.py"))
    voters = [p.read_text() for p in
              random.Random(voter_seed).sample(pool, min(N_VOTERS, len(pool)))]
    voters.append((BENCH / pid / "reference.py").read_text())
    with ThreadPoolExecutor(16) as ex:
        votes = list(ex.map(lambda s: outputs(s, problem, cands), voters))
    res = []
    for i in range(len(cands)):
        top, n = Counter(v[i] for v in votes).most_common(1)[0]
        ok = top != "!err" and n / len(votes) >= AGREE
        res.append((ok, json.loads(top) if ok else None))
    return res


def sample(pid: str, src: str, n: int = N_DRAWS) -> dict:
    """src = a builder (its generator.py, voters seed 1, outside T) or "heldout"
    (augment._gen, voters seed 0, outside T+). Cached in cache/D_<pid>_<src>.json (not tracked);
    without it, the sample is drawn and labelled again, the same, in about 10 s."""
    f = CACHE / f"D_{pid}_{src}.json"
    if f.exists():
        return json.loads(f.read_text())
    seed = f"{pid}:oracle_theory:{src}"
    if src == "heldout":
        rng = random.Random(seed)
        draws, avoid, vseed = [_typed(pid, _gen(pid, rng)) for _ in range(n)], tplus_keys(pid), 0
    else:
        draws, err = _draw((BENCH / pid / "amplified" / src / "generator.py").read_text(), seed, n)
        assert len(draws) == n, err
        avoid, vseed = held_keys(pid), 1
    keys = [_key(t) for t in draws]
    uniq = {k: t for k, t in zip(keys, draws) if k not in avoid}
    cands = list(uniq.values())
    problem = load_problem(pid, str(BENCH))
    ref = outputs((BENCH / pid / "reference.py").read_text(), problem, cands)
    lab = label(pid, cands, vseed)
    inputs = [dict(t, ref_ok=r != "!err", agree=a, expected=y)
              for t, r, (a, y) in zip(cands, ref, lab)]
    idx = {k: i for i, k in enumerate(uniq)}
    res = {"pid": pid, "src": src, "seed": seed, "n_draws": n, "inputs": inputs,
           "draws": [idx.get(k, -1) for k in keys]}      # -1: in T (or T+)
    CACHE.mkdir(exist_ok=True)
    f.write_text(json.dumps(res))
    return res


def kept(s: dict) -> tuple[list[dict], list[int]]:
    """D's support in the sample and each input's multiplicity among the draws."""
    mult = Counter(i for i in s["draws"] if i >= 0)
    ids = [i for i, t in enumerate(s["inputs"]) if t["ref_ok"] and t["agree"]]
    return [s["inputs"][i] for i in ids], [mult[i] for i in ids]


def failing(code: str, problem: dict, tests: list[dict]) -> list[int]:
    """Indices of tests the program fails (wrong, raises, times out), in chunks."""
    bad = []
    for i in range(0, len(tests), CHUNK):
        part = tests[i:i + CHUNK]
        r = run_tests(code, dict(problem, tests=part))
        if r.error is not None:                    # crashed or harness timeout: all fail
            bad += range(i, i + len(part))
        else:
            bad += sorted({i + f["index"] for f in r.failures})
    return bad


def strip(t: dict) -> dict:
    return {k: v for k, v in t.items() if k in ("args", "entry", "expected")}


if __name__ == "__main__":
    # self-check: our labelling reproduces gm's stored R3 T_amp from its own seed
    from src.experiments.augment import _fresh
    pid, m = "refactory_q3", "gpt-5.4-mini"
    code = (BENCH / pid / "amplified" / m / "generator.py").read_text()
    cands = _fresh(_draw(code, f"{pid}:llm")[0], held_keys(pid))
    problem = load_problem(pid, str(BENCH))
    ref = _outputs((BENCH / pid / "reference.py").read_text(), problem, cands)
    cands = [t for t, o in zip(cands, ref) if o != "!err"]
    mine = [dict(t, expected=y) for t, (a, y) in zip(cands, label(pid, cands, 1)) if a][:100]
    stored = json.loads((BENCH / pid / "amplified" / m / "tests.json").read_text())
    assert mine == stored, "labelling differs from augment.amplified_tests"
    print("ok: reproduces", pid, m, "tests.json")
