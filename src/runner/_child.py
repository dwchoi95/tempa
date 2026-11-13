"""Child process that executes one candidate program against a test suite.

Invoked by ``src.runner.testing.run_tests`` with a JSON payload path. Prints a
single JSON line: ``{passed, total, failures, error}``. Never raises out of the
student program: any exception becomes a failure record.
"""
import contextlib
import io
import json
import signal
import sys

from _values import Repr, decode, encode   # this script's own directory

# Algorithmic submissions recurse far deeper than CPython's default 1000;
# judges raise this, so a correct program must not be failed for it.
sys.setrecursionlimit(20000)


# ---------------------------------------------------------------- comparison
def _eq(a, b, tol):
    """Type-strict equality, floats within tol: a tuple is not a list and
    False is not 0, as the instructor's printed outputs tell them apart."""
    if isinstance(b, Repr):
        return repr(a) == b
    if type(a) is not type(b):
        return False
    if isinstance(a, float):
        return a == b or abs(a - b) <= tol
    if isinstance(a, (list, tuple)):
        return len(a) == len(b) and all(_eq(x, y, tol) for x, y in zip(a, b))
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(_eq(a[k], b[k], tol) for k in a)
    return a == b


def _encode(x):
    try:
        return encode(x)
    except RecursionError:
        return {"__repr__": "<unencodable>"}


def _num(tok):
    try:
        return float(tok)
    except (TypeError, ValueError):
        return None


def _stdout_eq(got, want, tol):
    """Judge-style comparison: whitespace-normalized, numeric tokens by tolerance."""
    g, w = got.split(), want.split()
    if len(g) != len(w):
        return False
    for a, b in zip(g, w):
        if a == b:
            continue
        fa, fb = _num(a), _num(b)
        if fa is None or fb is None or abs(fa - fb) > tol:
            return False
    return True


# ---------------------------------------------------------------- execution
def _run_call(src, entry, tests, tol, stop_early, per_test, prelude=""):
    ns = {}
    try:
        if prelude:               # the assignment's own globals, as its harness runs it
            exec(compile(prelude, "<prelude>", "exec"), ns)
        exec(compile(src, "<candidate>", "exec"), ns)
    except BaseException as e:  # syntax errors, import errors, top-level crashes
        return None, f"{type(e).__name__}: {e}"
    failures, passed = [], 0
    # Per-test wall clock: a buggy candidate can loop forever, so bound every
    # call the same way the stdio/file modes do — without this, an infinite loop
    # hangs the whole search until the outer subprocess timeout fires.
    have_timer = hasattr(signal, "setitimer")
    if have_timer:
        signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(_Timeout()))
    for i, t in enumerate(tests):
        fn = ns.get(t.get("entry", entry))
        if not callable(fn):
            failures.append({"index": i, "error": "NameError: entry not defined"})
            if stop_early:
                break
            continue
        args = decode(t.get("args", []))
        buf = io.StringIO()
        if have_timer:
            signal.setitimer(signal.ITIMER_REAL, per_test)
        try:
            with contextlib.redirect_stdout(buf):
                got = fn(*args)
        except _Timeout:
            failures.append({"index": i, "timeout": True})
            if stop_early:
                break
            continue
        except BaseException as e:
            failures.append({"index": i, "error": f"{type(e).__name__}: {e}"})
            if stop_early:
                break
            continue
        finally:
            if have_timer:
                signal.setitimer(signal.ITIMER_REAL, 0)
        if _eq(got, decode(t.get("expected")), tol):
            passed += 1
        else:
            failures.append({"index": i, "got": _encode(got),
                             "expected": t.get("expected")})
            if stop_early:
                break
    return (passed, failures), None


class _Timeout(Exception):
    pass


def _make_stdin(text):
    """stdin that supports BOTH ``input()`` and ``sys.stdin.buffer.read()``.

    Competitive submissions routinely use the binary fast-I/O idiom, so a plain
    StringIO (no ``.buffer``) would mark correct programs as crashing.
    """
    return io.TextIOWrapper(io.BytesIO(text.encode()), encoding="utf-8",
                            newline=None)


def _run_stdio(src, tests, tol, stop_early, per_test):
    try:
        code = compile(src, "<candidate>", "exec")
    except BaseException as e:
        return None, f"{type(e).__name__}: {e}"
    failures, passed = [], 0
    real_stdin = sys.stdin

    def _alarm(signum, frame):
        raise _Timeout()

    have_timer = hasattr(signal, "setitimer")
    if have_timer:
        signal.signal(signal.SIGALRM, _alarm)

    for i, t in enumerate(tests):
        buf = io.StringIO()
        sys.stdin = _make_stdin(t.get("stdin", ""))
        if have_timer:
            signal.setitimer(signal.ITIMER_REAL, per_test)
        try:
            with contextlib.redirect_stdout(buf):
                exec(code, {"__name__": "__main__"})
        except SystemExit:
            pass  # judge programs legitimately call exit()
        except _Timeout:
            failures.append({"index": i, "timeout": True})
            if stop_early:
                break
            continue
        except BaseException as e:
            failures.append({"index": i, "error": f"{type(e).__name__}: {e}"})
            if stop_early:
                break
            continue
        finally:
            if have_timer:
                signal.setitimer(signal.ITIMER_REAL, 0)
            sys.stdin = real_stdin
        got = buf.getvalue()
        if _stdout_eq(got, t.get("expected", ""), tol):
            passed += 1
        else:
            failures.append({"index": i, "got": got[:400],
                             "expected": str(t.get("expected", ""))[:400]})
            if stop_early:
                break
    sys.stdin = real_stdin
    return (passed, failures), None


def _run_file(src, tests, tol, stop_early, per_test):
    """Programs that read input.txt and write output.txt (Codeforces file mode).

    Each test runs in a scratch cwd with input.txt seeded; output.txt is read
    back and compared like stdout.
    """
    import os
    import tempfile
    try:
        code = compile(src, "<candidate>", "exec")
    except BaseException as e:
        return None, f"{type(e).__name__}: {e}"
    failures, passed = [], 0
    have_timer = hasattr(signal, "setitimer")
    if have_timer:
        signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(_Timeout()))
    cwd0 = os.getcwd()
    for i, t in enumerate(tests):
        d = tempfile.mkdtemp()
        with open(os.path.join(d, "input.txt"), "w") as fh:
            fh.write(t.get("stdin", ""))
        os.chdir(d)
        buf = io.StringIO()
        if have_timer:
            signal.setitimer(signal.ITIMER_REAL, per_test)
        try:
            with contextlib.redirect_stdout(buf):
                exec(code, {"__name__": "__main__"})
        except SystemExit:
            pass
        except _Timeout:
            os.chdir(cwd0)
            failures.append({"index": i, "timeout": True})
            if stop_early:
                break
            continue
        except BaseException as e:
            os.chdir(cwd0)
            failures.append({"index": i, "error": f"{type(e).__name__}: {e}"})
            if stop_early:
                break
            continue
        finally:
            if have_timer:
                signal.setitimer(signal.ITIMER_REAL, 0)
        outp = os.path.join(d, "output.txt")
        got = open(outp).read() if os.path.exists(outp) else buf.getvalue()
        os.chdir(cwd0)
        if _stdout_eq(got, t.get("expected", ""), tol):
            passed += 1
        else:
            failures.append({"index": i, "got": got[:400],
                             "expected": str(t.get("expected", ""))[:400]})
            if stop_early:
                break
    os.chdir(cwd0)
    return (passed, failures), None


def _all_pass(source, mode, entry, tests, tol, per_test, prelude="") -> tuple[bool, bool]:
    """(passes every test, ran past a per-test time limit)."""
    if mode == "stdio":
        out, err = _run_stdio(source, tests, tol, True, per_test)
    elif mode == "file":
        out, err = _run_file(source, tests, tol, True, per_test)
    else:
        out, err = _run_call(source, entry, tests, tol, True, per_test, prelude)
    if err is not None or out is None:
        return False, False
    passed, failures = out
    return (passed == len(tests) and len(tests) > 0,
            any(f.get("timeout") for f in failures))


def _main_batch(payload):
    """Test many candidates; stop after `max_pass` of them pass every test."""
    mode, entry, tests = payload["mode"], payload.get("entry"), payload["tests"]
    tol, per_test = payload["tol"], payload.get("per_test", 2.0)
    max_pass = payload.get("max_pass", 1)
    flags, hung, hits = [], [], 0
    for src in payload["sources"]:
        ok = h = False
        try:
            ok, h = _all_pass(src, mode, entry, tests, tol, per_test,
                              payload.get("prelude", ""))
        except BaseException:            # a bad candidate must not kill the batch
            ok = False
        flags.append(ok)
        hung.append(h)
        if ok:
            hits += 1
            if hits >= max_pass:         # enough passing candidates collected
                break
    print(json.dumps({"pass": flags, "hung": hung}))


def main():
    payload = json.load(open(sys.argv[1]))
    if payload.get("batch"):
        return _main_batch(payload)
    tests = payload["tests"]
    tol, stop_early = payload["tol"], payload["stop_early"]
    per_test = payload.get("per_test", 2.0)
    lines = set()
    if payload.get("trace"):          # the program's lines this run executes, each recorded once
        mon = sys.monitoring
        mon.use_tool_id(3, "trace")
        mon.register_callback(3, mon.events.LINE, lambda c, n: (
            lines.add(n) if c.co_filename == "<candidate>" else None, mon.DISABLE)[1])
        mon.set_events(3, mon.events.LINE)
    if payload["mode"] == "stdio":
        out, err = _run_stdio(payload["source"], tests, tol, stop_early, per_test)
    elif payload["mode"] == "file":
        out, err = _run_file(payload["source"], tests, tol, stop_early, per_test)
    else:
        out, err = _run_call(payload["source"], payload["entry"], tests, tol,
                             stop_early, per_test, payload.get("prelude", ""))
    if err is not None:
        print(json.dumps({"passed": 0, "total": len(tests), "failures": [], "error": err}))
        return
    passed, failures = out
    print(json.dumps({"passed": passed, "total": len(tests),
                      "failures": failures, "error": None, "lines": sorted(lines)}))


if __name__ == "__main__":
    main()
