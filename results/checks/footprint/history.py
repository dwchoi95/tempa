"""Whether a program's outcome on a test depends on the tests run before it. The harness runs a program's tests in one
namespace (src/runner/_child.py); here every test of T+ also runs alone, in a fresh namespace, on R1-R5: every correct
program (the voters' pool), every stored repair, and the T-passing candidates of the 100 pools of certified.py. `differ` counts programs that pass or fail some test differently.
    python3 -I history.py REPO   -> history.txt"""
import csv, json, sys
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path[:0] = [str(REPO), str(REPO / "src/runner")]
from src.runner import _child as C                         # noqa: E402
from src.experiments._common import ORDER, load_problem    # noqa: E402
from src.runner.testing import FLOAT_TOL                   # noqa: E402
POOL = REPO / "results/checks/oracle_theory/a4_pool"
CS1 = ORDER[:5]; M = ("claude-sonnet-5", "gpt-5.4-mini")
ARMS = ("tempa_l", "tempa_lf", "pydex", "refactory", "direct_llm")


def outcome(src, entry, tests, prelude):
    r, err = C._run_call(src, entry, tests, FLOAT_TOL, False, 2.0, prelude)
    if r is None:
        return None
    return {f["index"] for f in r[1]}


def job(a):
    kind, pid, model, src = a
    p = load_problem(pid, str(REPO / "benchmark"), model)
    tests, entry, pre = p["tests"], p.get("entry"), p.get("prelude", "")
    shared = outcome(src, entry, tests, pre)
    if shared is None:
        return kind, "no module", None
    alone = set()
    for i, t in enumerate(tests):
        o = outcome(src, entry, [t], pre)
        if o is None or o:
            alone.add(i)
    return kind, "same" if alone == shared else "differ", None if alone == shared else (pid, model, src[:400], sorted(alone ^ shared)[:6])


if __name__ == "__main__":
    jobs = []
    for pid in CS1:
        for m in M:
            seen = set()
            for b in sorted((REPO / "benchmark" / pid / "correct").glob("*.py")):
                seen.add(b.read_text()); jobs.append(("correct", pid, m, b.read_text()))
            for arm in ARMS:
                f = REPO / "results" / pid / f"{arm}.csv"
                if f.exists():
                    for r in csv.DictReader(f.open()):
                        if r["Fixed"] == "True" and r["Patch"] and r["Model"] in (m, "none") and r["Patch"] not in seen:
                            seen.add(r["Patch"]); jobs.append(("repair", pid, m, r["Patch"]))
            for l in open(POOL / f"{pid}_{m}.jsonl"):
                for c, _ in json.loads(l)["tpass"]:
                    if c not in seen:
                        seen.add(c); jobs.append(("pool", pid, m, c))
    with Pool(10) as pool:
        got = pool.map(job, jobs, chunksize=20)
    c = Counter((k, v) for k, v, _ in got)
    ex = [e for _, _, e in got if e][:5]
    out = [str(sorted(c.items())), f"examples: {json.dumps(ex)[:1800]}"]
    print("\n".join(out)); (Path(__file__).resolve().parent / "history.txt").write_text("\n".join(out) + "\n")
