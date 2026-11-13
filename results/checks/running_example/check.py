"""The running example of the Introduction and Section 2, the submission wrong_1_042 of sequential
search: the rule of Figure 1 and the rule it rejects, the repairs of Figure 2 and the two-rule repair of
Section 2.2, the correct program it is paired with, what the existing techniques returned for it, and
the two claims of the type checker. No model call.
    python3 -I results/checks/running_example/check.py   -> check.txt"""
import csv, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
from src.core import rulelang as RL                                     # noqa: E402
from src.core.repair import SearchBudget, repair                        # noqa: E402
from src.core.synthesis import load_fixer, pair_by_bfs, select_sample_pairs  # noqa: E402
from src.experiments._common import load_problem                        # noqa: E402
from src.runner.testing import run_tests                                # noqa: E402
from src.utils.metrics import rps                                       # noqa: E402

csv.field_size_limit(10**9)
PID, MODEL, KEY = "refactory_q1", "gpt-5.4-mini", "wrong_1_042"
OTHER = "claude-sonnet-5"
D = ROOT / "benchmark" / PID
tests = lambda f: (lambda x: x if isinstance(x, list) else x["tests"])(json.load(open(f)))
T = load_problem(PID)
Tp = load_problem(PID, str(ROOT / "benchmark"), MODEL)
held = dict(T, tests=tests(D / "heldout.json"))
amp = dict(T, tests=Tp["tests"][Tp["n_instructor"]:])


def score(src):
    return {k: f"{run_tests(src, p).passed}/{len(p['tests'])}" for k, p in (("T", T), ("generated", amp), ("held-out", held))}


def run(src, *args):
    env = {}
    exec(src, env)
    return env["search"](*args)


names = sorted(f.stem for f in (D / "buggy").glob("*.py"))
sources = [(D / "buggy" / f"{n}.py").read_text() for n in names]
correct = [f.read_text() for f in sorted((D / "correct").glob("*.py"))]
buggy = sources[names.index(KEY)]
partner, _ = pair_by_bfs(sources, correct)
nearest = correct[int(partner[names.index(KEY)])]
in_s = buggy in {s[0] for s in select_sample_pairs(sources, correct)}

tool = load_fixer(ROOT / "tools" / PID / MODEL / "fixer.rules")
A = repair(buggy, T, tool, SearchBudget())
B = repair(buggy, Tp, tool, SearchBudget())
x = (3, [3])
out = [f"Figure 2a (buggy): {score(buggy)}; representative of its cluster: {in_s}",
       f"nearest correct program: {score(nearest)}; search{x} = {run(nearest, *x)}",
       f"Two-rule repair (Section 2.2): rules {list(A.rules)} RPS {rps(buggy, A.patch):.4f} {score(A.patch)} search{x} = {run(A.patch, *x)}",
       f"Figure 2d: rules {list(B.rules)} RPS {rps(buggy, B.patch):.4f} {score(B.patch)} search{x} = {run(B.patch, *x)}"]
rows = lambda file, model=None: next(r for r in csv.DictReader(open(ROOT / "results" / PID / file)) if r["Buggy"] == KEY and (model is None or r["Model"] == model))
other = dict(T, tests=load_problem(PID, str(ROOT / "benchmark"), OTHER)["tests"][Tp["n_instructor"]:])
r = rows("refactory.csv"); out += [f"Figure 2b (Refactory): RPS {r['RPS']} {score(r['Patch'])}; on the {OTHER} suite {run_tests(r['Patch'], other).passed}/100; search{x} = {run(r['Patch'], *x)}"]
r = rows("pydex.csv", MODEL); out += [f"Figure 2c (PyDex, {MODEL}): RPS {r['RPS']} {score(r['Patch'])}; API ${r['$API']}"]
r = rows("pydex.csv", OTHER); out += [f"PyDex, {OTHER}: RPS {r['RPS']} T {run_tests(r['Patch'], T).passed}/{len(T['tests'])} generated {run_tests(r['Patch'], other).passed}/100 held-out {run_tests(r['Patch'], held).passed}/100"]
r = rows("tempa_l.csv", OTHER); out += [f"TEMPA_L, {OTHER} builder: {r['Source']} RPS {r['RPS']} T {run_tests(r['Patch'], T).passed}/{len(T['tests'])} generated {run_tests(r['Patch'], other).passed}/100 held-out {run_tests(r['Patch'], held).passed}/100"]

text = (ROOT / "tools" / PID / MODEL / "fixer.rules").read_text()
guess = 'rule b\nmatch: return len($seq) + 1\nrewrite: return len(seq)\n'
r3 = RL.compile_rules((ROOT / "tools" / "refactory_q3" / OTHER / "fixer.rules").read_text())[0]
out += [f"writing seq for $seq: {RL.compile_rules(guess)[1]}",
        f"R3 rule stray_double_equals_init, scope effect {RL.effect(next(r for r in r3 if r.name == 'stray_double_equals_init'))}"]
(HERE / "check.txt").write_text("\n".join(out) + "\n")
print("\n".join(out))
