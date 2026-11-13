"""Check the footprint theorem on every repair of every arm: run each buggy program
(traced) and each repair on the same inputs, and record the outcomes.  Resumable:
programs already in cache/<pid>.jsonl are skipped.
    python3 -I run.py REPO [WORKERS]"""
import csv, glob, hashlib, json, os, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); W = int(sys.argv[2]) if len(sys.argv) > 2 else 16
HERE = Path(__file__).resolve().parent; CACHE = HERE / "cache"; CACHE.mkdir(exist_ok=True)
ARMS = ["tempa_l", "tempa_lf", "refactory", "pydex", "direct_llm"]
PER_TEST = 2.0


def sha(s):
    return hashlib.sha1(s.encode()).hexdigest()[:16]


def inputs(pid):
    b = REPO / "benchmark" / pid
    prob = json.loads((b / "problem.json").read_text())
    ins = list(prob["tests"])
    for f in sorted(b.glob("amplified/*/tests.json")) + [b / "heldout.json", b / "boundary.json"]:
        if f.exists():
            ins += json.loads(f.read_text())
    return prob, ins


def child(job):
    pid, h, src, prob, ins, trace = job
    mode = prob.get("mode") or ("stdio" if ins and "stdin" in ins[0] else "call")
    pay = {"src": src, "mode": mode, "entry": prob.get("entry"), "prelude": prob.get("prelude", ""),
           "inputs": ins, "per_test": PER_TEST if mode != "call" else 0.5, "tol": 1e-6, "trace": trace}
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        json.dump(pay, fh)
    try:
        r = subprocess.run([sys.executable, "-I", str(HERE / "child.py"), fh.name], capture_output=True,
                           text=True, timeout=PER_TEST * len(ins) * 1.5 + 30)
        res = json.loads(r.stdout.strip().splitlines()[-1]) if r.stdout.strip() else {"error": r.stderr[-300:]}
    except subprocess.TimeoutExpired:
        res = {"error": "harness timeout"}
    finally:
        os.unlink(fh.name)
    return pid, h, trace, res


def main():
    jobs = []
    for pdir in sorted((REPO / "benchmark").glob("*/problem.json")):
        pid = pdir.parent.name
        prob, ins = inputs(pid)
        done = set()
        cf = CACHE / f"{pid}.jsonl"
        if cf.exists():
            done = {json.loads(l)["sha"] for l in cf.open()}
        progs = {}
        for f in sorted((REPO / "benchmark" / pid / "buggy").glob("*.py")):
            s = f.read_text(); progs[sha(s)] = (s, True)
        for arm in ARMS:
            f = REPO / "results" / pid / f"{arm}.csv"
            if f.exists():
                for r in csv.DictReader(f.open()):
                    if r["Fixed"] == "True" and r["Patch"]:
                        progs.setdefault(sha(r["Patch"]), (r["Patch"], False))
        for h, (s, tr) in progs.items():
            if h not in done:
                jobs.append((pid, h, s, prob, ins, tr))
    print(f"{len(jobs)} programs to run", flush=True)
    t0, n = time.time(), 0
    with ThreadPoolExecutor(W) as ex:
        futs = [ex.submit(child, j) for j in jobs]
        for fu in as_completed(futs):
            pid, h, tr, res = fu.result()
            with (CACHE / f"{pid}.jsonl").open("a") as fh:
                fh.write(json.dumps({"sha": h, "trace": tr, **res}) + "\n")
            n += 1
            if n % 500 == 0 or n == len(jobs):
                el = time.time() - t0
                print(f"{n}/{len(jobs)} {el:.0f}s elapsed, eta {el / n * (len(jobs) - n):.0f}s", flush=True)


if __name__ == "__main__":
    main()
