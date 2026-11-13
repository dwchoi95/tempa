"""Independent held-out suite for C1-C6 and a re-judgement of every arm's existing
repairs on it. CPU only, no LLM call. Repairs are not recomputed.

    python3 cf_heldout.py suites    # suites/<pid>.json + suites/stats_<pid>.json
    python3 cf_heldout.py collect   # rows.csv: every (arm, model, pid, buggy) on C1-C6 with its patch sha1
    python3 cf_heldout.py estimate  # time a sample, extrapolate the judge stage
    python3 cf_heldout.py judge     # cache/<pid>.json: sha1 -> verdict (resumable)
    python3 cf_heldout.py refactory # cache/refactory_shim_<pid>.json: Refactory's patches in its own harness
    python3 cf_heldout.py report    # CSVs + summary tables
    python3 cf_heldout.py all

Suite (per problem): inputs from gens.gen (written from the statement), seeded
random.Random("cf_heldout:<pid>"); 300 distinct candidates, none equal (as a token
sequence) to an official test; each labelled by up to 40 correct programs
(random.Random("cf_heldout_voters:<pid>"), excluding the correct programs the
builders were shown as worked fixes, synthesis.select_sample_pairs) and kept only
if >= 90% of them agree (C5, C6: both of their 2 programs) and the majority output
equals gens.ref; the first 100 kept, in draw order. Label = gens.ref's output.
Patch texts: ablation._arms (as results/ablation.csv), ablation._compose
(gate 0.25), results/<pid>/tempa_l.csv, results/<pid>/refactory.csv (unwrapped, as
augment.check runs Refactory's patches).
"""
import hashlib, importlib.util, json, os, random, sys, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pandas as pd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for d in ("suites", "cache", "logs"):
    (HERE / d).mkdir(exist_ok=True)
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(HERE)); os.chdir(ROOT)
from src.experiments._common import IDS, ORDER, load_pool, load_problem  # noqa
from src.runner.testing import run_tests  # noqa
import gens  # noqa

CF = ORDER[5:]
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
N_CAND, N_KEEP, N_VOTERS, AGREE = 300, 100, 40, 0.9
SENT = "__no_such_output__"
WORKERS = 16


def sha(p):
    return hashlib.sha1(p.encode()).hexdigest()


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def toks(s):
    return tuple(s.split())


# ------------------------------------------------------------------ suites
def outputs(src, prob, stdins, chunk=50):
    """Each input's stdout as a token tuple, '!err' on error/timeout."""
    out = []
    for i in range(0, len(stdins), chunk):
        part = stdins[i:i + chunk]
        res = run_tests(src, dict(prob, tests=[{"stdin": s, "expected": SENT} for s in part]))
        got = ["!err"] * len(part)
        if res.error is None:
            for f in res.failures:
                if "got" in f:
                    got[f["index"]] = toks(f["got"])
        out += got
    return out


def shown_fixes(pid):
    """Correct programs the builder saw as worked fixes (both builders see the same pairs)."""
    from src.core.synthesis import select_sample_pairs
    return {f for _b, f, _n in select_sample_pairs(load_pool(pid, "buggy"), load_pool(pid, "correct"))}


def suite(pid):
    f = HERE / "suites" / f"{pid}.json"
    if f.exists():
        return
    prob = load_problem(pid)
    official = {toks(t["stdin"]) for t in prob["tests"]}
    rng, seen, cands = random.Random(f"cf_heldout:{pid}"), set(), []
    drawn = dup_off = dup_self = 0
    while len(cands) < N_CAND and drawn < 200000:
        cls, s = gens.gen(pid, rng)
        drawn += 1
        assert gens.valid(pid, s), (pid, s)
        k = toks(s)
        if k in official:
            dup_off += 1
        elif k in seen:
            dup_self += 1
        else:
            seen.add(k)
            cands.append((cls, s))
    shown = shown_fixes(pid)
    paths = sorted((ROOT / "benchmark" / pid / "correct").glob("*.py"))
    pool = [p for p in paths if p.read_text() not in shown]
    if len(pool) < 2:                     # C5, C6: 2 correct programs, both needed
        pool = paths
    voters = random.Random(f"cf_heldout_voters:{pid}").sample(pool, min(N_VOTERS, len(pool)))
    need = 1.0 if len(voters) <= 2 else AGREE
    stdins = [s for _c, s in cands]
    with ThreadPoolExecutor(WORKERS) as ex:
        votes = list(ex.map(lambda p: outputs(p.read_text(), prob, stdins), voters))
    kept, why, agree_all, agree_kept = [], Counter(), [], []
    voter_wrong = Counter()
    for i, (cls, s) in enumerate(cands):
        top, n = Counter(v[i] for v in votes).most_common(1)[0]
        a = n / len(votes)
        agree_all.append(a)
        r = toks(gens.ref(pid, s))
        if top == "!err":
            why["majority error/timeout"] += 1
        elif a < need:
            why[f"agreement < {need:.0%}"] += 1
        elif top != r:
            why["majority != reference"] += 1
        elif len(kept) < N_KEEP:
            kept.append({"stdin": s, "expected": gens.ref(pid, s) + "\n", "cls": cls,
                         "agree": a})
            agree_kept.append(a)
            for j, v in enumerate(votes):
                if v[i] != r:
                    voter_wrong[voters[j].stem] += 1
        else:
            why["beyond the first 100"] += 1
    stats = {"pid": pid, "id": IDS[pid], "drawn": drawn, "dup_official": dup_off,
             "dup_earlier_draw": dup_self, "candidates": len(cands), "kept": len(kept),
             "dropped": dict(why), "pool": len(paths), "shown_to_builder": len(shown),
             "voters": len(voters), "need": need,
             "agree_mean_cands": sum(agree_all) / len(agree_all),
             "unanimous_cands": sum(a == 1 for a in agree_all),
             "agree_mean_kept": sum(agree_kept) / max(1, len(agree_kept)),
             "agree_min_kept": min(agree_kept, default=None),
             "unanimous_kept": sum(a == 1 for a in agree_kept),
             "voters_wrong_on_some_kept": len(voter_wrong),
             "classes_kept": dict(Counter(t["cls"] for t in kept)),
             "voter_files": [p.name for p in voters]}
    (HERE / "suites" / f"stats_{pid}.json").write_text(json.dumps(stats, indent=1))
    f.write_text(json.dumps(kept, indent=1))
    log(f"{IDS[pid]} {pid}: drawn {drawn}, {len(cands)} candidates, kept {len(kept)}, "
        f"dropped {dict(why)}, voters {len(voters)} (pool {len(paths)}, shown {len(shown)})")


# ------------------------------------------------------------------ collect
def _gate_compose():
    from src.experiments import ablation

    def compose(local, direct, gate):
        saved = ablation.RPS_GATE
        ablation.RPS_GATE = gate
        try:
            return ablation._compose(local, direct)
        finally:
            ablation.RPS_GATE = saved
    return compose


def collect():
    from src.experiments.ablation import _arms, _log
    from src.experiments.refactory_results import unwrap
    compose = _gate_compose()
    out, texts = [], {}
    for pid in CF:
        arms = {("TEMPA_LF" if a == "full" else a): v for a, v in _arms(pid).items()
                if not a.endswith("(run)")}
        direct = _log(pid, "direct_llm")
        arms["gate 0.25"] = compose(_log(pid, "tempa_l"), direct, 0.25)
        arms["gate 0.25 -rules"] = compose(_log(pid, "tempa_l_fw"), direct, 0.25)
        arms["TEMPA_L"] = _log(pid, "tempa_l")
        r = pd.read_csv(ROOT / "results" / pid / "refactory.csv", keep_default_na=False)
        arms["Refactory"] = {(m, str(x.Buggy)): {"fixed": str(x.Fixed) == "True",
                                                 "patch": unwrap(str(x.Patch)) if str(x.Fixed) == "True" else "",
                                                 "rps": float(x.RPS) if str(x.Fixed) == "True" else None}
                             for _, x in r.iterrows() for m in MODELS}
        for arm, got in arms.items():
            for (m, b), v in got.items():
                h = sha(v["patch"]) if v["fixed"] else ""
                if v["fixed"]:
                    texts.setdefault(pid, {})[h] = v["patch"]
                out.append({"arm": arm, "pid": pid, "model": m, "buggy": b, "fixed": v["fixed"],
                            "rps_check": v["rps"], "sha": h})
        log(f"{IDS[pid]}: {len(arms)} arms, {len(texts[pid])} distinct repaired texts")
    pd.DataFrame(out).rename(columns={"rps_check": "rps"}).to_csv(HERE / "rows.csv", index=False)
    (HERE / "cache" / "texts.json").write_text(json.dumps(texts))


# ------------------------------------------------------------------ judge
def _verdict(src, off, ind):
    t0 = time.time()
    a = run_tests(src, off)
    b = run_tests(src, ind)
    fails = [{"i": f["index"], "kind": "timeout" if f.get("timeout") else
              ("error" if f.get("error") else "wrong"),
              "got": f.get("got", f.get("error", ""))[:200]} for f in b.failures]
    return {"off": a.all_pass, "off_err": a.error, "ind": b.all_pass, "ind_err": b.error,
            "ind_passed": b.passed, "ind_total": b.total, "fails": fails[:20],
            "timeoutish": bool(b.error) or any(f["kind"] == "timeout" for f in fails) or
                          (not a.all_pass and (bool(a.error) or any(f.get("timeout") for f in a.failures))),
            "sec": time.time() - t0}


def problems(pid):
    prob = load_problem(pid)
    ind = json.loads((HERE / "suites" / f"{pid}.json").read_text())
    return prob, dict(prob, tests=[{"stdin": t["stdin"], "expected": t["expected"]} for t in ind])


def estimate(k=60):
    texts = json.loads((HERE / "cache" / "texts.json").read_text())
    tot_est, lines = 0.0, []
    for pid in CF:
        off, ind = problems(pid)
        todo = sorted(texts[pid].items())
        sample = random.Random(0).sample(todo, min(k, len(todo)))
        t0 = time.time()
        with ThreadPoolExecutor(WORKERS) as ex:
            res = list(ex.map(lambda kv: _verdict(kv[1], off, ind), sample))
        wall = time.time() - t0
        est = wall * len(todo) / len(sample)
        tot_est += est
        lines.append(f"{IDS[pid]}: {len(todo)} distinct texts; sample {len(sample)} in {wall:.1f}s "
                     f"wall ({WORKERS} workers, mean {sum(r['sec'] for r in res)/len(res):.2f}s cpu-ish each)"
                     f" -> est {est/60:.1f} min")
    lines.append(f"ESTIMATE judge stage: {tot_est/60:.1f} min wall clock "
                 f"(+ a sequential re-run of any timeout-ish verdict)")
    for l in lines:
        log(l)
    (HERE / "logs" / "estimate.txt").write_text("\n".join(lines) + "\n")


def judge():
    texts = json.loads((HERE / "cache" / "texts.json").read_text())
    t_all = time.time()
    for pid in CF:
        f = HERE / "cache" / f"{pid}.json"
        have = json.loads(f.read_text()) if f.exists() else {}
        todo = {h: p for h, p in texts[pid].items() if h not in have}
        off, ind = problems(pid)
        log(f"{IDS[pid]}: {len(have)} cached, {len(todo)} to judge")
        t0, done = time.time(), 0
        with ThreadPoolExecutor(WORKERS) as ex:
            for h, v in zip(todo, ex.map(lambda p: _verdict(p, off, ind), todo.values())):
                have[h] = v
                done += 1
                if done % 200 == 0:
                    f.write_text(json.dumps(have))
                    log(f"  {IDS[pid]}: {done}/{len(todo)} ({time.time()-t0:.0f}s)")
        f.write_text(json.dumps(have))
        # a timeout under load is not a wrong answer: re-run those alone, keep the second verdict
        again = [h for h, v in have.items() if v.get("timeoutish") and "rerun" not in v]
        for h in again:
            v2 = _verdict(texts[pid][h], off, ind)
            have[h] = dict(v2, rerun=True, first={k: have[h][k] for k in ("off", "ind")})
        f.write_text(json.dumps(have))
        log(f"{IDS[pid]}: judged {len(todo)} in {time.time()-t0:.0f}s; re-ran {len(again)} timeout-ish alone")
    log(f"judge stage wall clock {time.time()-t_all:.0f}s")


def refactory_shim():
    """Refactory's C1-C6 'fixed' comes from its own harness (core_testing.Tester):
    global.py (imports, exit -> _Exit, print/input shims) + the wrapped patch +
    `_feed(stdin) ; main() ; _flush()`. Judge its patches the same way, on the
    official tests and the suite: cache/refactory_shim_<pid>.json, sha1(raw patch)."""
    for pid in CF:
        f = HERE / "cache" / f"refactory_shim_{pid}.json"
        have = json.loads(f.read_text()) if f.exists() else {}
        r = pd.read_csv(ROOT / "results" / pid / "refactory.csv", keep_default_na=False)
        raw = {sha(p): p for p, ok in zip(r.Patch.astype(str), r.Fixed.astype(str)) if ok == "True"}
        front = (ROOT / "baselines/refactory/data_cf" / pid / "code/global.py").read_text()
        todo = {h: front + "\n" + p + "\n_feed(sys.stdin.read()) ; main() ; _flush()\n"
                for h, p in raw.items() if h not in have}
        off, ind = problems(pid)
        t0 = time.time()
        with ThreadPoolExecutor(WORKERS) as ex:
            have.update(zip(todo, ex.map(lambda p: _verdict(p, off, ind), todo.values())))
        f.write_text(json.dumps(have))
        log(f"{IDS[pid]}: Refactory harness judged {len(todo)} raw patches in {time.time()-t0:.0f}s; "
            f"official {sum(v['off'] for v in have.values())}/{len(have)}, "
            f"suite {sum(v['ind'] for v in have.values())}/{len(have)}")


if __name__ == "__main__":
    step = sys.argv[1] if len(sys.argv) > 1 else "all"
    t = time.time()
    if step in ("suites", "all"):
        for pid in CF:
            suite(pid)
    if step in ("collect", "all") and not (HERE / "rows.csv").exists():
        collect()
    if step == "estimate":
        estimate()
    if step in ("judge", "all"):
        judge()
    if step in ("refactory", "all"):
        refactory_shim()
    if step in ("report", "all"):
        import report
        report.main()
    log(f"step {step} done in {time.time()-t:.0f}s")
