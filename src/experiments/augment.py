"""`run.py augment` — the two suites R1-R5 add to the instructor's tests.

R1-R5 ship 7.4 instructor tests per assignment. Both suites draw inputs from a
generator and label each by differential testing -- the majority output of a
sample of the class's correct programs plus the instructor's reference -- and
keep an input only where at least 90% of them agree, so an input outside the
specification (where correct programs disagree) never becomes a test.

* The **amplified** suite is part of TEMPA (Section III-D): the builder writes
  the generator (benchmark/<pid>/amplified/<model>/generator.py), and the
  suite (tests.json) joins T in every acceptance check (`--amplified`).
* The **held-out** suite is the evaluation's (benchmark/<pid>/heldout.json):
  our own generator, another seed and voter sample, and no input in common
  with any amplified suite, so no arm has searched against it.

C1-C6 need neither: their suites are Codeforces' full official test sets.

    python run.py augment instructor                 # T: benchmark/<pid>/problem.json
    python run.py augment heldout                    # benchmark/<pid>/heldout.json
    python run.py augment boundary                   # relabel benchmark/<pid>/boundary.json
    python run.py augment amplify --model M          # benchmark/<pid>/amplified/M/
    python run.py augment check                      # results/heldout.csv
    python run.py augment pairs                      # results/heldout_pairs.csv

`amplify` relabels the stored generator.py when there is one, so it needs no
API key; `--regenerate` asks the builder for a new generator.
"""
from __future__ import annotations

import argparse
import ast
import json
import random
import subprocess
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd

from src.experiments._common import load_env, load_problem
from src.prompts import render
from src.experiments.refactory_results import unwrap
from src.runner._values import SOURCE as VALUES, decode, encode
from src.runner.testing import run_tests
from src.utils import llm as llm_mod

ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / "benchmark"
REFACTORY = ROOT / "baselines" / "refactory" / "data"
CS1 = ["refactory_q1", "refactory_q2", "refactory_q3", "refactory_q4", "refactory_q5"]
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
N_CAND, N_KEEP, N_VOTERS, AGREE = 300, 100, 40, 0.9
SENTINEL = "__no_such_output__"
MONTHS = ["January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December"]


def _gen(pid: str, rng: random.Random) -> dict:
    """One random test input in the assignment's own calling convention."""
    if pid == "refactory_q1":                  # search(x, sorted seq)
        seq = sorted(rng.sample(range(-15, 16), rng.randint(0, 7)))
        return {"args": [rng.randint(-20, 20), seq]}
    if pid == "refactory_q2":                  # birthdays as [month, day] pairs
        pb = [[rng.choice(MONTHS[:5]), str(rng.randint(1, 6))]
              for _ in range(rng.randint(1, 6))]
        pb = [list(p) for p in dict.fromkeys(map(tuple, pb))]
        entry = rng.choice(["unique_day", "unique_month", "contains_unique_day"])
        key = (str(rng.randint(1, 6)) if entry == "unique_day"
               else rng.choice(MONTHS[:5]))
        return {"args": [key, pb], "entry": entry}
    if pid == "refactory_q3":                  # remove_extras(lst)
        return {"args": [[rng.randint(0, 5) for _ in range(rng.randint(0, 8))]]}
    if pid == "refactory_q4":                  # sort_age([[gender, age], ...])
        ages = rng.sample(range(1, 90), rng.randint(0, 6))
        return {"args": [[[rng.choice("MF"), a] for a in ages]]}
    if pid == "refactory_q5":                  # top_k(lst, k)
        lst = [rng.randint(0, 9) for _ in range(rng.randint(0, 9))]
        return {"args": [lst, rng.randint(0, len(lst))]}
    raise ValueError(pid)


def _convention(pid: str, args: list) -> list:
    """Arguments in the types the instructor's tests use: R1's sequence and R2's
    birthdays are tuples, R4's people (gender, age) tuples."""
    if pid == "refactory_q1":
        return [args[0], tuple(args[1])]
    if pid == "refactory_q2":
        return [args[0], tuple(tuple(p) for p in args[1])]
    if pid == "refactory_q4":
        return [[tuple(p) for p in args[0]]]
    return args


def _typed(pid: str, t: dict) -> dict:
    return dict(t, args=[encode(a) for a in _convention(pid, t["args"])])


def instructor() -> None:
    """T of R1-R5: Refactory's released tests (data/question_<q>/ans), with their
    tuples kept, and global.py run before every program as Refactory's harness
    does; a test that names one of its constants gets the literal it holds."""
    for q, pid in enumerate(CS1, 1):
        qd, p = REFACTORY / f"question_{q}", BENCH / pid / "problem.json"
        prob = json.loads(p.read_text())
        g = qd / "code" / "global.py"
        prelude = g.read_text() if g.exists() else ""
        consts = {n.targets[0].id: ast.literal_eval(n.value) for n in ast.parse(prelude).body
                  if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)}
        tests = []
        for inp in sorted((qd / "ans").glob("input_*.txt")):
            call = ast.parse(inp.read_text().strip(), mode="eval").body
            args = [consts[a.id] if isinstance(a, ast.Name) else ast.literal_eval(a)
                    for a in call.args]
            out = (qd / "ans" / inp.name.replace("input_", "output_")).read_text().strip()
            t = {"args": [encode(a) for a in args], "expected": encode(ast.literal_eval(out))}
            if call.func.id != prob["entry"]:
                t["entry"] = call.func.id
            tests.append(t)
        p.write_text(json.dumps(dict(prob, tests=tests, prelude=prelude), indent=1))
        print(f"{pid}: {len(tests)} instructor tests")


def boundary() -> None:
    """The hand-written boundary suites (benchmark/<pid>/boundary.json) in the
    instructor's types, relabelled by the instructor's solution."""
    for pid in CS1:
        f, problem = BENCH / pid / "boundary.json", load_problem(pid, str(BENCH))
        tests = [_typed(pid, dict(t, args=[decode(a) for a in t["args"]]))
                 for t in json.loads(f.read_text())]
        outs = _outputs((BENCH / pid / "reference.py").read_text(), problem, tests)
        kept = [dict(t, expected=json.loads(o)) for t, o in zip(tests, outs) if o != "!err"]
        f.write_text(json.dumps(kept, indent=1))
        print(f"{pid}: {len(kept)} boundary tests")


def _outputs(src: str, problem: dict, tests: list[dict]) -> list[str]:
    """Each test's output as a JSON string ('!err' on an error or timeout)."""
    probe = dict(problem, tests=[dict(t, expected=SENTINEL) for t in tests])
    res = run_tests(src, probe)
    out = ["!err"] * len(tests)
    for f in res.failures:
        if "got" in f:
            out[f["index"]] = json.dumps(f["got"], sort_keys=True)
    return out


def _key(t: dict) -> str:
    """A test's input, without its expected output."""
    return json.dumps({k: v for k, v in t.items() if k != "expected"}, sort_keys=True)


def _fresh(inputs, seen: set[str]) -> list[dict]:
    """Up to N_CAND distinct inputs not already in seen (which it extends)."""
    cands = []
    for t in inputs:
        k = _key(t)
        if k not in seen:
            seen.add(k)
            cands.append(t)
            if len(cands) == N_CAND:
                break
    return cands


def _vote(pid: str, cands: list[dict], voter_seed: int,
          pool_dir: Path | None = None) -> list[dict]:
    """Up to N_KEEP of cands, each labelled by the voters' majority output.

    Voters are a sample of the correct programs in pool_dir (default: the whole
    class) plus the instructor's reference.
    """
    problem = load_problem(pid, str(BENCH))
    pool = sorted((pool_dir or BENCH / pid / "correct").glob("*.py"))
    voters = [p.read_text() for p in
              random.Random(voter_seed).sample(pool, min(N_VOTERS, len(pool)))]
    voters.append((BENCH / pid / "reference.py").read_text())
    with ThreadPoolExecutor(16) as ex:
        votes = list(ex.map(lambda s: _outputs(s, problem, cands), voters))
    kept = []
    for i, t in enumerate(cands):
        top, n = Counter(v[i] for v in votes).most_common(1)[0]
        if top != "!err" and n / len(votes) >= AGREE:
            kept.append(dict(t, expected=json.loads(top)))
        if len(kept) == N_KEEP:
            break
    return kept


_DRAW = """
import json, random, sys
rng, out, err = random.Random(sys.argv[1]), [], None
for _ in range(int(sys.argv[2])):
    try:
        t = gen(rng)
        if isinstance(t, dict) and isinstance(t.get("args"), (list, tuple)):
            t = dict(t, args=[encode(a) for a in t["args"]])
        out.append(t)
    except Exception as e:
        err = err or f"{type(e).__name__}: {e}"
print("\\n" + json.dumps({"inputs": out, "error": err}))
"""


def _draw(code: str, seed: str, n: int = 20 * N_CAND) -> tuple[list[dict], str | None]:
    """n calls of the generated gen(rng), in a child process; (inputs, first error)."""
    try:
        r = subprocess.run([sys.executable, "-c", code + "\n" + VALUES + _DRAW, seed, str(n)],
                           capture_output=True, text=True, timeout=120)
        res = json.loads(r.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        return [], f"gen did not return {n} inputs within 120 s"
    except (json.JSONDecodeError, IndexError):
        return [], (r.stderr.strip().splitlines() or ["gen produced no output"])[-1]
    ok = [t for t in res["inputs"] if isinstance(t, dict) and isinstance(t.get("args"), list)
          and set(t) <= {"args", "entry"}]
    if len(ok) < len(res["inputs"]):
        res["error"] = res["error"] or 'gen returned something other than {"args": [...]}'
    return ok, res["error"]


def held_keys(pid: str) -> set[str]:
    """Inputs an amplified suite must avoid: T alone. Amplify runs at deployment,
    where no evaluation suite exists, so it must not see the held-out one; the
    held-out suite avoids T+ instead (heldout())."""
    return {_key(t) for t in load_problem(pid, str(BENCH))["tests"]}


def amplified_tests(pid: str, code: str, pool_dir: Path | None = None) -> list[dict]:
    """T_amp from a builder's generator: draws (seed `<pid>:llm`) the reference
    accepts, none in T, labelled by the voters (seed 1) drawn from pool_dir
    (default: the whole class)."""
    problem = load_problem(pid, str(BENCH))
    reference = (BENCH / pid / "reference.py").read_text()
    inputs, _ = _draw(code, f"{pid}:llm")
    cands = _fresh(inputs, held_keys(pid))
    outs = _outputs(reference, problem, cands) if cands else []
    return _vote(pid, [t for t, o in zip(cands, outs) if o != "!err"], 1, pool_dir)


def _ask_builder(pid: str, model: str, rounds: int = 3) -> tuple[str, dict]:
    """The builder writes gen(rng); validate it against the reference and refine.

    A round fails if gen raises, returns a malformed input, or the reference
    rejects more than 10% of its inputs; the next round sees why. The round
    with the most inputs the reference accepts is kept.
    """
    problem = load_problem(pid, str(BENCH))
    reference = (BENCH / pid / "reference.py").read_text()
    best, cost, feedback = ("", -1), {"in": 0, "out": 0, "usd": 0.0, "s": 0.0}, ""
    for rnd in range(rounds):
        call = llm_mod.complete(render(
            "input_gen", description=problem.get("description", ""), reference=reference,
            tests="\n".join(json.dumps(t) for t in problem["tests"]), feedback=feedback),
            model=model)
        for k, a in (("in", "in_tokens"), ("out", "out_tokens"), ("usd", "usd"), ("s", "seconds")):
            cost[k] += getattr(call, a)
        code = call.code or ""
        inputs, err = _draw(code, f"{pid}:llm")
        cands = _fresh(inputs, held_keys(pid))
        outs = _outputs(reference, problem, cands) if cands else []
        rejected = [t for t, o in zip(cands, outs) if o == "!err"]
        print(f"  {pid} {model} round {rnd + 1}: {len(cands)} distinct, "
              f"{len(rejected)} rejected by the reference" + (f", error: {err}" if err else ""))
        if len(cands) - len(rejected) > best[1]:
            best = (code, len(cands) - len(rejected))
        if not err and cands and len(rejected) <= 0.1 * len(cands):
            best = (code, len(cands))                  # a round that passes beats any that failed
            break
        why = err or (f"the reference raised an error or timed out on {len(rejected)} of "
                      f"{len(cands)} inputs, e.g. {json.dumps(rejected[:3])}" if cands
                      else "it produced no new inputs")
        feedback = (f"\n## This is a refinement round\nYour previous generator:\n"
                    f"```python\n{code}\n```\nIt failed because {why}.\n")
    cost["rounds"] = rnd + 1
    return best[0], cost


def tplus_keys(pid: str) -> set[str]:
    """Inputs of T and of either builder's T_amp, which an evaluation suite avoids."""
    keys = held_keys(pid)
    for m in MODELS:
        f = BENCH / pid / "amplified" / m / "tests.json"
        keys |= {_key(t) for t in json.loads(f.read_text())} if f.exists() else set()
    return keys


def heldout() -> None:
    """The held-out evaluation suite: benchmark/<pid>/heldout.json, disjoint from
    T and from both builders' T_amp (run after amplify)."""
    for pid in CS1:
        problem = load_problem(pid, str(BENCH))
        rng = random.Random(pid)
        cands = _fresh(iter(lambda: _typed(pid, _gen(pid, rng)), None), tplus_keys(pid))
        kept = _vote(pid, cands, 0)
        (BENCH / pid / "heldout.json").write_text(json.dumps(kept, indent=1))
        print(f"{pid}: {len(problem['tests'])} instructor + {len(kept)} held-out tests")


def amplify(model: str, regenerate: bool = False, root: Path = BENCH) -> None:
    """TEMPA's amplified suite: <root>/<pid>/amplified/<model>/{generator.py,
    tests.json, cost.json}, root = benchmark/ for the campaign. Everything it
    uses -- the class's correct programs, the reference, and the builder -- is
    available at deployment."""
    for pid in CS1:
        d = Path(root) / pid / "amplified" / model
        gen = d / "generator.py"
        if regenerate or not gen.exists():
            load_env()
            code, cost = _ask_builder(pid, model)
            d.mkdir(parents=True, exist_ok=True)
            gen.write_text(code)
            (d / "cost.json").write_text(json.dumps(cost))
        kept = amplified_tests(pid, gen.read_text())
        (d / "tests.json").write_text(json.dumps(kept, indent=1))
        print(f"{pid} {model}: {len(kept)} amplified tests")


# (event file, arm) judged on the held-out suite; no_amplification/ holds the
# same arms accepting against T alone
ARMS = [("refactory", "Refactory"), ("pydex", "PyDex"), ("direct_llm", "LLM_Direct"),
        ("tempa_l_fw", "TEMPA_L_fw"), ("tempa_l", "TEMPA_L"), ("tempa_lf", "TEMPA_LF"),
        ("no_amplification/direct_llm", "LLM_Direct (T)"),
        ("no_amplification/tempa_l", "TEMPA_L (T)"), ("no_amplification/tempa_lf", "TEMPA_LF (T)")]


def _suite(pid: str, name: str = "heldout") -> dict:
    """T plus the held-out tests (or plus benchmark/<pid>/<name>.json), less any
    input already in T+, so the suite measures correctness beyond the tests."""
    problem, seen = load_problem(pid, str(BENCH)), tplus_keys(pid)
    extra = json.loads((BENCH / pid / f"{name}.json").read_text())
    return dict(problem, tests=problem["tests"] + [t for t in extra if _key(t) not in seen])


def check(name: str = "heldout") -> pd.DataFrame:
    """Re-run every arm's repairs on T plus the held-out suite -> results/heldout.csv
    (or plus the <name> suite -> results/<name>.csv)."""
    rows = []
    for pid in CS1:
        suite = _suite(pid, name)
        for stem, arm in ARMS:
            f = ROOT / "results" / pid / f"{stem}.csv"
            if not f.exists():
                continue
            d = pd.read_csv(f, keep_default_na=False)
            ok = d[d.Fixed.astype(str) == "True"]
            patches = {p: None for p in ok.Patch.astype(str)}
            unwrap_ = stem == "refactory"

            def passes(p: str) -> bool:
                r = run_tests(unwrap(p) if unwrap_ else p, suite)
                return r.error is None and r.total > 0 and r.passed == r.total

            with ThreadPoolExecutor(16) as ex:
                verdict = dict(zip(patches, ex.map(passes, patches)))
            for model, g in d.groupby(d.Model.astype(str)):
                gok = g[g.Fixed.astype(str) == "True"]
                rows.append({"pid": pid, "arm": arm, "model": model, "n": len(g),
                             "fixed": len(gok),
                             "fixed_heldout": int(sum(verdict[p] for p in gok.Patch.astype(str)))})
            print(f"{pid} {arm}: " + ", ".join(
                f"{r['model']} {r['fixed']}->{r['fixed_heldout']}" for r in rows
                if r["pid"] == pid and r["arm"] == arm))
    df = pd.DataFrame(rows)
    df.to_csv(ROOT / "results" / f"{name}.csv", index=False)
    return df


def pairs(name: str = "heldout") -> pd.DataFrame:
    """Per-program held-out verdicts of TEMPA_LF against PyDex and against TEMPA_LF
    accepting T alone: exact McNemar on held-out repair, and Wilcoxon on RPS over
    the programs both arms repaired that survive. -> results/heldout_pairs.csv
    """
    from scipy.stats import binomtest, wilcoxon

    def verdicts(f: Path, suite: dict) -> dict:
        d = pd.read_csv(f, keep_default_na=False)
        ok = [r for _, r in d[d.Fixed.astype(str) == "True"].iterrows()]
        with ThreadPoolExecutor(16) as ex:
            got = ex.map(lambda r: run_tests(r.Patch, suite).all_pass, ok)
        return {(r.Model, str(r.Buggy)): (v, float(r.RPS)) for r, v in zip(ok, got)}

    arms = {"tempa_lf": "tempa_lf", "pydex": "pydex", "tempa_lf_t": "no_amplification/tempa_lf"}
    rows = []
    for pid in CS1:
        suite = _suite(pid, name)
        got = {a: verdicts(ROOT / "results" / pid / f"{stem}.csv", suite)
               for a, stem in arms.items()}
        for m in MODELS:
            for b in sorted(p.stem for p in (BENCH / pid / "buggy").glob("*.py")):
                row = {"pid": pid, "model": m, "buggy": b}
                for a in arms:
                    row[a], row[f"{a}_rps"] = got[a].get((m, b), (False, None))
                rows.append(row)
    df = pd.DataFrame(rows)
    df.to_csv(ROOT / "results" / f"{name}_pairs.csv", index=False)
    for name, g in [*df.groupby("model"), ("pooled", df)]:
        for other in ("pydex", "tempa_lf_t"):
            b10 = int((g.tempa_lf & ~g[other]).sum())
            b01 = int((~g.tempa_lf & g[other]).sum())
            p = binomtest(min(b10, b01), b10 + b01).pvalue if b10 + b01 else 1.0
            print(f"{name}: held-out RR TEMPA_LF {100 * g.tempa_lf.mean():.1f} vs {other} "
                  f"{100 * g[other].mean():.1f} (McNemar b={b10}, c={b01}, p={p:.2g})")
        c = g[g.tempa_lf & g.pydex]
        print(f"{name}: RPS on {len(c)} common survivors {c.tempa_lf_rps.mean():.3f} vs PyDex "
              f"{c.pydex_rps.mean():.3f} (Wilcoxon p={wilcoxon(c.tempa_lf_rps, c.pydex_rps).pvalue:.2g})")
    return df


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py augment")
    ap.add_argument("action", choices=["instructor", "heldout", "boundary", "amplify",
                                       "check", "pairs"])
    ap.add_argument("--model", default="claude-sonnet-5", help="amplify: the builder")
    ap.add_argument("--regenerate", action="store_true",
                    help="amplify: ask the builder for a new generator")
    ap.add_argument("--root", default=str(BENCH),
                    help="amplify: where to write <pid>/amplified/<model>/ (a rebuild)")
    ap.add_argument("--suite", default="heldout",
                    help="check/pairs: the suite beside T (benchmark/<pid>/<suite>.json)")
    args = ap.parse_args(argv)
    if args.action in ("check", "pairs"):
        {"check": check, "pairs": pairs}[args.action](args.suite)
    else:
        {"instructor": instructor, "heldout": heldout, "boundary": boundary}.get(
            args.action, lambda: amplify(args.model, args.regenerate, Path(args.root)))()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
