"""Differential run of the Lean Surf interpreter (`pycore run`, Surf/Semantics.lean with Ref.interp)
against CPython on the buggy programs and TEMPA's repairs (arms tempa_l, tempa_lf), on their test inputs
(problem.json `tests`, plus heldout.json). Writes difftest.jsonl (one line per program) and
difftest.txt (counts). CPython's runs are cached in cpython_cache.jsonl (1.3 GB for all programs,
not tracked); a program not in it is run again, only slower. PYCORE names the pycore binary
(default: mech/.lake/build/bin/pycore of this repository).

    python3 -I difftest.py REPO [--limit N] [--pid PID] [--jobs J] [--fuel F]
"""
import ast, hashlib, io, json, os, signal, struct, subprocess, sys, tempfile, contextlib
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "lean_cls"))
from progs import programs                      # noqa: E402
from export_surf import Exporter                # noqa: E402

PER_TEST = 2.0


# ------------------------------------------------------------------ values

def decode(x):
    if isinstance(x, list):
        return [decode(v) for v in x]
    if isinstance(x, dict):
        if len(x) == 1 and next(iter(x)) in ("__tuple__", "__set__", "__dict__", "__repr__"):
            (k, v), = x.items()
            if k == "__tuple__":
                return tuple(decode(e) for e in v)
            if k == "__set__":
                return {decode(e) for e in v}
            if k == "__dict__":
                return {decode(a): decode(b) for a, b in v}
            raise ValueError("repr value")
        return {k: decode(v) for k, v in x.items()}
    return x


def q(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def sx(v):
    if v is None:
        return "(none)"
    if isinstance(v, bool):
        return f"(bool {int(v)})"
    if isinstance(v, int):
        return f'(int "{v}")'
    if isinstance(v, float):
        return f'(float "{struct.unpack("<Q", struct.pack("<d", v))[0]}")'
    if isinstance(v, str):
        return f"(str {q(v)})"
    if isinstance(v, list):
        return "(list " + " ".join(map(sx, v)) + ")"
    if isinstance(v, tuple):
        return "(tuple " + " ".join(map(sx, v)) + ")"
    if isinstance(v, (set, frozenset)):
        return "(set " + " ".join(map(sx, v)) + ")"
    if isinstance(v, dict):
        return "(dict " + " ".join(f"({sx(a)} {sx(b)})" for a, b in v.items()) + ")"
    raise ValueError(type(v).__name__)


def canon(x):
    """As Ref.canon: repr, a set's elements sorted; objects with an address as <object>."""
    t = type(x)
    if t is tuple:
        return "(" + canon(x[0]) + ",)" if len(x) == 1 else "(" + ", ".join(map(canon, x)) + ")"
    if t is list:
        return "[" + ", ".join(map(canon, x)) + "]"
    if t is dict:
        return "{" + ", ".join(canon(k) + ": " + canon(v) for k, v in x.items()) + "}"
    if t in (set, frozenset):
        return "set()" if not x else "{" + ", ".join(sorted(map(canon, x))) + "}"
    r = repr(x)
    return "<object>" if " at 0x" in r else r


# ------------------------------------------------------------------ CPython

class _Timeout(BaseException):
    pass


def _alarm(*_):
    raise _Timeout()


def cpython(src, prelude, mode, tests, skip=()):
    """CPython 3.13's outcome of every test, as _child.py runs them. In call mode the
    tests after a timeout are not run (the interrupted test left the state undefined);
    the tests in `skip` are not run either."""
    sys.setrecursionlimit(20000)
    signal.signal(signal.SIGALRM, _alarm)
    res = []
    real_stdin = sys.stdin
    try:
        code = compile(src, "<candidate>", "exec")
    except BaseException as e:
        return [{"st": "compile", "exc": type(e).__name__}]
    if mode == "stdio":
        for i, t in enumerate(tests):
            if i in skip:
                res.append({"st": "timeout", "out": ""})
                continue
            buf = io.StringIO()
            sys.stdin = io.TextIOWrapper(io.BytesIO(t["stdin"].encode()), encoding="utf-8", newline=None)
            signal.setitimer(signal.ITIMER_REAL, PER_TEST)
            st, extra = "ok", {}
            try:
                with contextlib.redirect_stdout(buf):
                    exec(code, {"__name__": "__main__"})
            except SystemExit:
                pass
            except _Timeout:
                st = "timeout"
            except BaseException as e:
                st, extra = "exc", {"exc": type(e).__name__}
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
                sys.stdin = real_stdin
            res.append({"st": st, "out": buf.getvalue(), **extra})
        return res
    ns = {}
    sys.stdin = io.StringIO("")
    buf = io.StringIO()
    signal.setitimer(signal.ITIMER_REAL, 10.0)
    try:
        with contextlib.redirect_stdout(buf):
            if prelude:
                exec(compile(prelude, "<prelude>", "exec"), ns)
            exec(code, ns)
    except _Timeout:
        return [{"st": "module-timeout", "out": buf.getvalue()}]
    except BaseException as e:
        return [{"st": "module-exc", "out": buf.getvalue(), "exc": type(e).__name__}]
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    dead = False
    for i, t in enumerate(tests):
        if dead or i in skip:
            res.append({"st": "timeout", "out": ""})
            continue
        fn = ns.get(t["entry"])
        if not callable(fn):
            res.append({"st": "noentry", "out": ""})
            continue
        args = decode(t["args"])
        buf = io.StringIO()
        signal.setitimer(signal.ITIMER_REAL, PER_TEST)
        try:
            with contextlib.redirect_stdout(buf):
                got = fn(*args)
            res.append({"st": "ok", "out": buf.getvalue(), "val": canon(got)})
        except _Timeout:
            res.append({"st": "timeout", "out": buf.getvalue()})
            dead = True
        except BaseException as e:
            res.append({"st": "exc", "out": buf.getvalue(), "exc": type(e).__name__})
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
    sys.stdin = real_stdin
    return res


def cpython_child(payload, seed="0", skip=()):
    """Run in a fresh process (state of one program cannot leak into another), with a fixed
    string-hash seed."""
    env = dict(os.environ, PYTHONHASHSEED=seed)
    with tempfile.NamedTemporaryFile("r", suffix=".json", delete=False) as fh:
        out = fh.name
    try:
        p = subprocess.run([sys.executable, "-s", "-P", __file__, "--cpython", out],
                           input=json.dumps(dict(payload, skip=list(skip))),
                           capture_output=True, text=True, timeout=600, env=env)
        return json.loads(Path(out).read_text())
    except Exception as e:
        return [{"st": "crash", "err": str(e)[:300]}]
    finally:
        Path(out).unlink(missing_ok=True)


# ------------------------------------------------------------------ jobs

def export(src):
    tree = ast.parse(src)
    return Exporter().module(tree)


def problem(REPO, pid):
    d = json.loads((REPO / "benchmark" / pid / "problem.json").read_text())
    tests = list(d["tests"])
    h = REPO / "benchmark" / pid / "heldout.json"
    if h.exists():
        tests += json.loads(h.read_text())
    mode = d.get("mode") or ("stdio" if tests and "stdin" in tests[0] else "call")
    norm = []
    for t in tests:
        if mode == "stdio":
            norm.append({"stdin": t.get("stdin", "")})
        else:
            norm.append({"entry": t.get("entry", d.get("entry")), "args": t.get("args", [])})
    return mode, d.get("prelude", ""), norm


def job(src, prelude, mode, tests, fuel, py=None):
    """The Lean job; a test CPython timed out on is skipped (in call mode, with every later
    one, whose state the interrupted test left)."""
    p = export(src)
    pre = f"(prelude {export(prelude)})" if prelude else "(prelude)"
    ts = []
    for i, t in enumerate(tests):
        if py is not None and i < len(py) and py[i]["st"] == "timeout":
            ts.append("(skip)")
            if mode != "stdio":
                break
        elif mode == "stdio":
            ts.append(f"(stdin {q(t['stdin'])})")
        else:
            ts.append(f"(call {q(t['entry'])} ({' '.join(sx(a) for a in decode(t['args']))}))")
    return f"(job {mode} {fuel} {pre} {p} (tests {' '.join(ts)}))"


def lean(exe, jobs, timeout=1800):
    with tempfile.NamedTemporaryFile("w", suffix=".sx", delete=False) as fh:
        fh.write("\n".join(jobs))
        path = fh.name
    try:
        p = subprocess.run([exe, "run", path], capture_output=True, text=True, timeout=timeout)
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
        raise RuntimeError(f"lean gave {len(out)} of {len(jobs)} jobs: {p.stderr[-500:]}")
    return out


def lean_batch(args):
    exe, jobs = args
    try:
        return lean(exe, jobs)
    except Exception as e:      # a crash of one batch: run its jobs one by one
        res = []
        for j in jobs:
            try:
                res.append(lean(exe, [j], timeout=300)[0])
            except subprocess.TimeoutExpired:
                res.append([{"st": "lean-timeout"}])
            except Exception as e2:
                res.append([{"st": "lean-crash", "why": str(e2)[:200]}])
        return res


# ------------------------------------------------------------------ comparison

NOT_COVERED = {"unsup", "fuel", "depth", "after-fuel", "module-unsup", "module-fuel", "module-depth",
               "lean-timeout"}


def compare(py, ln, mode, py2=None):
    """Per test: agree, differ, or a not-covered reason. `py2` is CPython's run under another
    string-hash seed: a test whose outcome depends on it depends on set order of strings."""
    if py and py[0]["st"] == "compile":
        return ["unparsable"]
    if py and py[0]["st"] == "crash":
        return ["nc:timeout"]
    if py and py[0]["st"] in ("module-exc", "module-timeout"):
        if ln and ln[0]["st"].startswith("module-"):
            l0 = ln[0]
            if l0["st"] in NOT_COVERED:
                return ["nc:" + l0["st"] + ":" + l0.get("why", "")]
            if py[0]["st"] == "module-timeout":
                return ["nc:timeout"]
            ok = l0["st"] == "module-exc" and l0.get("exc") == py[0].get("exc") and l0.get("out") == py[0].get("out")
            return ["agree" if ok else "differ"]
        return ["differ"]
    if ln and ln[0]["st"] == "lean-timeout":
        return ["nc:lean-timeout"] * max(1, len(py))
    if ln and ln[0]["st"].startswith("module-"):
        l0 = ln[0]
        return ["nc:" + l0["st"] + ":" + l0.get("why", "")] if l0["st"] in NOT_COVERED else ["differ"]
    out = []
    for i, p in enumerate(py):
        l = ln[i] if i < len(ln) else {"st": "missing"}
        # a test whose CPython outcome changes with the string-hash seed is compared with the
        # seed-0 run (Ref's str hash is CPython's under PYTHONHASHSEED=0) and marked with `*`
        star = "*" if py2 is not None and i < len(py2) and py2[i] != p else ""
        if p["st"] == "timeout" or l["st"] == "skip":
            out.append("nc:timeout")
        elif l["st"] in NOT_COVERED:
            out.append("nc:" + l["st"] + ":" + l.get("why", ""))
        elif p["st"] != l["st"] or p.get("out") != l.get("out") or p.get("val") != l.get("val") or p.get("exc") != l.get("exc"):
            out.append("differ" + star)
        else:
            out.append("agree" + star)
    return out


def main():
    REPO = Path(sys.argv[1])
    argv = sys.argv[2:]
    opt = lambda k, d: type(d)(argv[argv.index(k) + 1]) if k in argv else d
    limit, pidf, jobsn, fuel = opt("--limit", 0), opt("--pid", ""), opt("--jobs", 8), opt("--fuel", 20000000)
    exe = os.environ.get("PYCORE", str(HERE.parents[2] / "mech/.lake/build/bin/pycore"))
    progs = [p for p in programs(REPO) if not pidf or p[0] == pidf]
    if limit:
        progs = progs[:limit]
    probs = {pid: problem(REPO, pid) for pid in {p[0] for p in progs}}
    # CPython first (cached by program): its timeouts are skipped in the Lean jobs
    payloads = [{"src": src, "prelude": probs[pid][1], "mode": probs[pid][0], "tests": probs[pid][2]}
                for pid, kind, src in progs]
    keys = [hashlib.sha1((pid + "\0" + src).encode()).hexdigest() for pid, kind, src in progs]
    cache_f = HERE / "cpython_cache.jsonl"
    cache = {}
    if cache_f.exists():
        for l in cache_f.open():
            r = json.loads(l)
            cache[r["key"]] = (r["py"], r["py2"])
    todo = [k for k, key in enumerate(keys) if key not in cache]
    with ProcessPoolExecutor(jobsn) as ex:
        new = list(ex.map(cpython_child, [payloads[k] for k in todo], chunksize=4))
        skips = [[i for i, r in enumerate(py) if r.get("st") == "timeout"] for py in new]
        new2 = list(ex.map(cpython_child, [payloads[k] for k in todo], ["1"] * len(todo), skips, chunksize=4))
    with cache_f.open("a") as fh:
        for k, a, b in zip(todo, new, new2):
            cache[keys[k]] = (a, b)
            fh.write(json.dumps({"key": keys[k], "py": a, "py2": b}) + "\n")
    pys = [cache[key][0] for key in keys]
    pys2 = [cache[key][1] for key in keys]
    items, jobs, pre = [], [], {}
    for k, (pid, kind, src) in enumerate(progs):
        mode, prelude, tests = probs[pid]
        rec = {"pid": pid, "kind": kind, "k": k}
        try:
            jobs.append(job(src, prelude, mode, tests, fuel, pys[k]))
            items.append(rec)
        except SyntaxError:
            pre[k] = "unparsable"
            items.append(rec)
            jobs.append(None)
        except NotImplementedError as e:
            pre[k] = "nc:excluded:" + str(e)
            items.append(rec)
            jobs.append(None)
    # Lean, in batches
    idx = [k for k, j in enumerate(jobs) if j is not None]
    # small batches for the judge problems (whose programs run long), large for the rest
    batches = []
    for mode in ("stdio", "call"):
        ks = [k for k in idx if probs[progs[k][0]][0] == mode]
        B = 4 if mode == "stdio" else 25
        batches += [ks[i:i + B] for i in range(0, len(ks), B)]
    with ProcessPoolExecutor(jobsn) as ex:
        outs = list(ex.map(lean_batch, [(exe, [jobs[k] for k in b]) for b in batches]))
    lns = {}
    for b, o in zip(batches, outs):
        for k, r in zip(b, o):
            lns[k] = r
    tot, byprob, reasons = Counter(), {}, Counter()
    with open(HERE / "difftest.jsonl", "w") as fh:
        for rec in items:
            k = rec["k"]
            mode = probs[rec["pid"]][0]
            res = [pre[k]] if k in pre else compare(pys[k], lns.get(k, []), mode, pys2[k])
            rec.update(res=res, py=pys[k], py2=pys2[k], lean=lns.get(k))
            fh.write(json.dumps(rec) + "\n")
            c = byprob.setdefault(rec["pid"], Counter())
            for r in res:
                if r.endswith("*"):
                    tot["seed-dependent"] += 1
                    c["seed-dependent"] += 1
                    r = r[:-1]
                key = "agree" if r == "agree" else "differ" if r == "differ" else "unparsable" if r == "unparsable" else "not covered"
                tot[key] += 1
                c[key] += 1
                if key == "not covered":
                    reasons[r] += 1
            res = [r.rstrip("*") for r in res]
            progkey = ("prog-differ" if "differ" in res else "prog-agree" if all(r == "agree" for r in res)
                       else "prog-unparsable" if res == ["unparsable"] else "prog-partly-not-covered")
            tot[progkey] += 1
            c[progkey] += 1
    lines = [f"programs {len(items)}", "tests " + json.dumps(dict(tot))]
    for pid in sorted(byprob):
        lines.append(f"{pid} " + json.dumps(dict(byprob[pid])))
    lines.append("not covered: " + json.dumps(dict(reasons.most_common())))
    (HERE / "difftest.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    if sys.argv[1:2] == ["--cpython"]:
        pl = json.loads(sys.stdin.read())
        r = cpython(pl["src"], pl["prelude"], pl["mode"], pl["tests"], set(pl.get("skip", [])))
        Path(sys.argv[2]).write_text(json.dumps(r))
    else:
        main()
