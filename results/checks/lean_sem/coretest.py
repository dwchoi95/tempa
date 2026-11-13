"""Differential run of Surf.Sem against PyCore on the translation (`pycore runcore`,
Surf/RunCore.lean), both under the traced reference interpretation, on the buggy programs and
TEMPA's repairs (as difftest.py takes them), on every test. A test CPython timed out on (from
difftest's CPython cache) is skipped, as difftest skips it. Writes coretest.jsonl and
coretest.txt. A program difftest.py has not run (cpython_cache.jsonl, 1.3 GB for all programs, is
not tracked) is first run on CPython here, as difftest.py runs it: the same result, only slower.
PYCORE names the pycore binary (default: mech/.lake/build/bin/pycore of this repository).

    python3 -I coretest.py REPO [--limit N] [--pid PID] [--jobs J] [--fuel F]
    python3 -I coretest.py REPO --retry [--jobs J] [--timeout S]   (rerun the timed-out programs)
    python3 -I coretest.py --src FILE.py [--stdin TEXT]...
"""
import hashlib, json, os, subprocess, sys, tempfile
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import difftest as D                            # noqa: E402

EXE = os.environ.get("PYCORE", str(HERE.parents[2] / "mech/.lake/build/bin/pycore"))


def run(jobs, timeout=1800):
    with tempfile.NamedTemporaryFile("w", suffix=".sx", delete=False) as fh:
        fh.write("\n".join(jobs))
        path = fh.name
    try:
        p = subprocess.run([EXE, "runcore", path], capture_output=True, text=True, timeout=timeout)
    finally:
        os.unlink(path)
    out, cur = [], None
    for l in p.stdout.splitlines():
        if l == "job":
            cur = []
        elif l == "end":
            out.append(cur)
            cur = None
        elif cur is not None:
            cur.append(json.loads(l))
    if len(out) != len(jobs):
        raise RuntimeError(f"pycore gave {len(out)} of {len(jobs)} jobs: {p.stderr[-500:]}")
    return out


def batch(jobs):
    try:
        return run(jobs)
    except Exception:
        res = []
        for j in jobs:
            try:
                res.append(run([j], timeout=600)[0])
            except subprocess.TimeoutExpired:
                res.append([{"core": "nc", "why": "timeout"}])
            except Exception as e:
                res.append([{"core": "crash", "why": str(e)[:200]}])
        return res


def verdicts(lines):
    out = []
    for l in lines:
        if "error" in l:
            out.append("error")
        elif l.get("st") == "skip":
            out.append("nc:cpython-timeout")
        elif l.get("st") == "after-fuel":
            out.append("nc:after-fuel")
        else:
            c = l.get("core", "nc")
            out.append(c if c in ("agree", "mismatch", "crash") else "nc:" + l.get("why", ""))
    return out


def one(j, timeout):
    try:
        return run([j], timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        return [{"core": "nc", "why": "timeout"}]


def summarize(items):
    tot, bykind, reasons, progs_c = Counter(), {}, Counter(), Counter()
    for rec in items:
        c = bykind.setdefault(rec["kind"], Counter())
        for r in rec["res"]:
            key = r if r in ("agree", "mismatch", "unparsable", "error", "crash") else "not covered"
            tot[key] += 1
            c[key] += 1
            if key == "not covered":
                reasons[r] += 1
        progs_c["prog-mismatch" if "mismatch" in rec["res"] else "prog-agree" if all(r == "agree" for r in rec["res"]) else "prog-other"] += 1
    lines = [f"programs {len(items)} " + json.dumps(dict(progs_c)), "tests " + json.dumps(dict(tot))]
    for kd in sorted(bykind):
        lines.append(f"{kd} " + json.dumps(dict(bykind[kd])))
    lines.append("not covered: " + json.dumps(dict(reasons.most_common())))
    (HERE / "coretest.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


def retry(REPO, jobsn, fuel, timeout):
    """Rerun, one job per process with `timeout` seconds, the programs a batch run left with
    a timeout or a crash, and update coretest.jsonl and coretest.txt."""
    items = [json.loads(l) for l in (HERE / "coretest.jsonl").open()]
    todo = [k for k, r in enumerate(items) if any(x in ("nc:timeout", "crash") for x in r["res"])]
    plist = D.programs(REPO)           # coretest.jsonl has one line per program, in this order
    assert len(plist) == len(items)
    cache = {}
    for l in (HERE / "cpython_cache.jsonl").open():
        r = json.loads(l)
        cache[r["key"]] = r["py"]
    jobs = []
    for k in todo:
        pid, kind, src = plist[k]
        assert (pid, kind) == (items[k]["pid"], items[k]["kind"])
        mode, prelude, tests = D.problem(REPO, pid)
        key = hashlib.sha1((pid + "\0" + src).encode()).hexdigest()
        jobs.append(D.job(src, prelude, mode, tests, fuel, cache.get(key)))
    with ProcessPoolExecutor(jobsn) as ex:
        outs = list(ex.map(one, jobs, [timeout] * len(jobs)))
    for k, o in zip(todo, outs):
        items[k]["lines"] = o
        items[k]["res"] = verdicts(o)
    with open(HERE / "coretest.jsonl", "w") as fh:
        for rec in items:
            fh.write(json.dumps(rec) + "\n")
    print(f"retried {len(todo)} programs")
    summarize(items)


def main():
    argv = sys.argv[1:]
    if "--retry" in argv:
        opt = lambda k, d: type(d)(argv[argv.index(k) + 1]) if k in argv else d
        retry(Path(argv[0]), opt("--jobs", 16), opt("--fuel", 20000000), opt("--timeout", 3600))
        return
    if argv[0] == "--src":
        src = Path(argv[1]).read_text()
        stdins = [argv[i + 1] for i, a in enumerate(argv) if a == "--stdin"] or [""]
        j = D.job(src, "", "stdio", [{"stdin": s} for s in stdins], 20000000)
        for l in run([j])[0]:
            print(json.dumps(l))
        return
    REPO = Path(argv[0])
    opt = lambda k, d: type(d)(argv[argv.index(k) + 1]) if k in argv else d
    limit, pidf, jobsn, fuel = opt("--limit", 0), opt("--pid", ""), opt("--jobs", 8), opt("--fuel", 20000000)
    allprogs = D.programs(REPO)
    progs = [p for p in allprogs if not pidf or p[0] == pidf]
    if limit:
        progs = progs[:limit]
    probs = {pid: D.problem(REPO, pid) for pid in {p[0] for p in progs}}
    modef = opt("--mode", "")
    merge = None
    if modef:
        # rerun the programs of one mode only, keeping the other lines of coretest.jsonl
        merge = [json.loads(l) for l in (HERE / "coretest.jsonl").open()]
        assert len(merge) == len(allprogs) and not limit and not pidf
        sel = [k for k, p in enumerate(allprogs) if probs[p[0]][0] == modef]
        progs = [allprogs[k] for k in sel]
    cache = {}
    cache_f = HERE / "cpython_cache.jsonl"
    for l in (cache_f.open() if cache_f.exists() else ()):
        r = json.loads(l)
        cache[r["key"]] = r["py"]
    key = lambda pid, src: hashlib.sha1((pid + "\0" + src).encode()).hexdigest()
    miss = [p for p in progs if key(p[0], p[2]) not in cache]
    if miss:                    # no CPython run from difftest.py: run CPython here, as difftest.py does
        with ProcessPoolExecutor(jobsn) as ex:
            got = ex.map(D.cpython_child, [{"src": s, "prelude": probs[p][1], "mode": probs[p][0], "tests": probs[p][2]}
                                           for p, _, s in miss], chunksize=4)
            cache.update((key(p, s), py) for (p, _, s), py in zip(miss, got))
    items, jobs = [], []
    for k, (pid, kind, src) in enumerate(progs):
        mode, prelude, tests = probs[pid]
        py = cache.get(hashlib.sha1((pid + "\0" + src).encode()).hexdigest())
        rec = {"pid": pid, "kind": kind, "key": hashlib.sha1((pid + "\0" + src).encode()).hexdigest()}
        try:
            jobs.append(D.job(src, prelude, mode, tests, fuel, py))
        except (SyntaxError, NotImplementedError) as e:
            rec["res"] = ["unparsable"]
            jobs.append(None)
        items.append(rec)
    idx = [k for k, j in enumerate(jobs) if j is not None]
    batches = []
    for mode in ("stdio", "call"):
        ks = [k for k in idx if probs[progs[k][0]][0] == mode]
        B = 4 if mode == "stdio" else 25
        batches += [ks[i:i + B] for i in range(0, len(ks), B)]
    with ProcessPoolExecutor(jobsn) as ex:
        outs = list(ex.map(batch, [[jobs[k] for k in b] for b in batches]))
    res = {}
    for b, o in zip(batches, outs):
        for k, r in zip(b, o):
            res[k] = r
    for k, rec in enumerate(items):
        if "res" not in rec:
            rec["lines"] = res.get(k, [])
            rec["res"] = verdicts(rec["lines"])
    if merge is not None:
        for k, rec in zip(sel, items):
            merge[k] = rec
        items = merge
    with open(HERE / "coretest.jsonl", "w") as fh:
        for rec in items:
            fh.write(json.dumps(rec) + "\n")
    summarize(items)

if __name__ == "__main__":
    main()
