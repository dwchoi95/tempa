"""A4: the effective pool behind the overfitting bound (R1-R5, whole-class tools).

pool : for a seeded sample of programs per (assignment, builder), run TEMPA_L's
       local search as the *canonical run* of Prop. oblivious (no candidate
       passes T+), logging every candidate it validates and its verdict on T.
       src/ is untouched: run_batch is wrapped in this process only (rule
       search: T stage real, T+ stage rejects all; transplant: each candidate
       judged on T, then rejected).
err  : every distinct T-passing candidate run on its builder's D (common.sample,
       15-20k labelled draws): err(c) = share of draws it fails, and its
       error set (failing inputs), which is all the bound's event depends on.
report: |C(b)|, T-passing, distinct error sets, and per eps the bound
       sum_{distinct sets, err > eps} (1-err)^n  <=  N_eff (1-eps)^n  vs  1,600 (1-eps)^n.
No LLM call.   python3 a4_pool.py pool 6 && python3 a4_pool.py err 12 && python3 a4_pool.py report
pool -> a4_pool/<pid>_<model>.jsonl, err -> a4_err/<pid>_<model>.json, report -> A4_pool_rows.csv
"""
import hashlib, json, os, random, sys
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import IDS, ORDER, load_pool, load_problem, tool_path  # noqa

HERE = Path(__file__).resolve().parent
POOL = HERE / "a4_pool"
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
CS1 = ORDER[:5]
PER = int(os.environ.get("A4_PER", 10))          # programs per (assignment, builder)
N, EPS, WORST = 100, (0.01, 0.05, 0.10), 1600
LOG = []


def sha(s):
    return hashlib.sha1(s.encode()).hexdigest()


def install():
    import src.core.reference_repair as F
    import src.core.repair as R
    from src.runner import testing
    real = testing.run_batch
    if getattr(R.run_batch, "a4", False):
        return

    def tplus(p):
        n = p.get("n_instructor")
        return n is not None and len(p["tests"]) > n

    def rule_rb(sources, problem, *a, hangs=False, **kw):
        if tplus(problem):                          # canonical run: T+ rejects all
            out = [False] * len(sources)
            return (out, [False] * len(sources)) if hangs else out
        res = real(sources, problem, *a, hangs=hangs, **kw)
        LOG.extend(("rule", s, f) for s, f in zip(sources, res[0] if hangs else res))
        return res

    def ref_rb(sources, problem, per_candidate_timeout=3.0, max_pass=1, **kw):
        t = dict(problem, tests=problem["tests"][:problem["n_instructor"]])
        flags = real(sources, t, per_candidate_timeout=per_candidate_timeout, max_pass=len(sources))
        LOG.extend(("ref", s, f) for s, f in zip(sources, flags))
        return [False] * len(sources)

    rule_rb.a4 = True
    R.run_batch, F.run_batch = rule_rb, ref_rb


_ctx = {}


def ctx(pid, m):
    if (pid, m) not in _ctx:
        from src.core.reference_repair import ReferenceIndex
        from src.core.synthesis import load_fixer
        _ctx[pid, m] = (load_problem(pid, "benchmark", m), load_fixer(tool_path(pid, m)),
                        ReferenceIndex(load_pool(pid, "correct")))
    return _ctx[pid, m]


def canon(pid, m, name):
    os.cpu_count = lambda: 3                        # 2 threads per batch
    install()
    from src.core.reference_repair import local_repair
    from src.core.repair import SearchBudget
    prob, rules, index = ctx(pid, m)
    src = (ROOT / "benchmark" / pid / "buggy" / f"{name}.py").read_text()
    LOG.clear()
    local_repair(src, prob, rules, index, SearchBudget())
    tp = {}
    for kind, s, ok in LOG:
        if ok:
            tp.setdefault(s, kind)
    return {"pid": pid, "model": m, "buggy": name, "validated": len(LOG),
            "rule": sum(k == "rule" for k, _, _ in LOG), "ref": sum(k == "ref" for k, _, _ in LOG),
            "distinct": len({s for _, s, _ in LOG}), "tpass": [[s, k] for s, k in tp.items()]}


def sample_names(pid, m):
    names = sorted(p.stem for p in (ROOT / "benchmark" / pid / "buggy").glob("*.py"))
    return random.Random(f"{pid}:{m}:a4").sample(names, min(PER, len(names)))


def phase_pool(nw):
    POOL.mkdir(parents=True, exist_ok=True)
    tasks = []
    for pid in CS1:
        for m in MODELS:
            f = POOL / f"{pid}_{m}.jsonl"
            done = {json.loads(l)["buggy"] for l in open(f)} if f.exists() else set()
            tasks += [(pid, m, n) for n in sample_names(pid, m) if n not in done]
    print(len(tasks), "programs", flush=True)
    with ProcessPoolExecutor(nw) as ex:
        for fu in as_completed([ex.submit(canon, *t) for t in tasks]):
            r = fu.result()
            with open(POOL / f"{r['pid']}_{r['model']}.jsonl", "a") as h:
                h.write(json.dumps(r) + "\n")
            print(r["pid"], r["model"], r["buggy"], r["validated"], len(r["tpass"]), flush=True)


def phase_err(nw):
    sys.path.insert(0, str(HERE))
    from common import failing, kept, sample, strip
    for pid in CS1:
        problem = load_problem(pid, "benchmark")
        for m in MODELS:
            ins, mult = kept(sample(pid, m))          # cached in oracle_theory/cache
            tests, tot = [strip(t) for t in ins], sum(mult)
            cands = {sha(s): s for l in open(POOL / f"{pid}_{m}.jsonl")
                     for s, _ in json.loads(l)["tpass"]}
            f = HERE / "a4_err" / f"{pid}_{m}.json"
            f.parent.mkdir(exist_ok=True)
            got = json.loads(f.read_text()) if f.exists() else {}
            left = [k for k in cands if k not in got]

            def one(k):
                bad = failing(cands[k], problem, tests)
                return [sum(mult[i] for i in bad) / tot, sha(json.dumps(bad))]
            with ThreadPoolExecutor(nw) as ex:
                for i, (k, v) in enumerate(zip(left, ex.map(one, left))):
                    got[k] = v
                    if i % 32 == 31:
                        f.write_text(json.dumps(got))
            f.write_text(json.dumps(got))
            print(pid, m, len(cands), "T-passing candidates; D =", len(tests), "inputs /", tot, "draws", flush=True)


def phase_report():
    import pandas as pd
    rows = []
    for pid in CS1:
        for m in MODELS:
            err = json.loads((HERE / "a4_err" / f"{pid}_{m}.json").read_text())
            lf = pd.read_csv(ROOT / "results" / pid / "tempa_l.csv", keep_default_na=False)
            lf = lf[lf.Model == m].set_index(lf[lf.Model == m].Buggy.astype(str))
            for l in open(POOL / f"{pid}_{m}.jsonl"):
                r = json.loads(l)
                e = {}                                  # error set -> err
                for s, _k in r["tpass"]:
                    v, sig = err[sha(s)]
                    e[sig] = v
                row = {"id": IDS[pid], "model": m, "buggy": r["buggy"], "validated": r["validated"],
                       "rule": r["rule"], "ref": r["ref"], "tpass": len(r["tpass"]),
                       "tpass_rule": sum(k == "rule" for _, k in r["tpass"]),
                       "distinct_sets": len(e), "err0": sum(v > 0 for v in e.values())}
                p = lf.Patch.get(r["buggy"], "")
                row["returned_in_pool"] = (not p) or any(s == p for s, _ in r["tpass"])
                for eps in EPS:
                    bad = [v for v in e.values() if v > eps]
                    row[f"Neff_{eps}"] = len(bad)
                    row[f"sharp_{eps}"] = min(1, sum((1 - v) ** N for v in bad))
                    row[f"eff_{eps}"] = min(1, len(e) * (1 - eps) ** N)
                    row[f"worst_{eps}"] = min(1, WORST * (1 - eps) ** N)
                rows.append(row)
    d = pd.DataFrame(rows)
    d.to_csv(HERE / "A4_pool_rows.csv", index=False)
    return d


if __name__ == "__main__":
    {"pool": lambda: phase_pool(int(sys.argv[2])), "err": lambda: phase_err(int(sys.argv[2])),
     "report": lambda: print(phase_report().describe().T.to_string())}[sys.argv[1]]()
