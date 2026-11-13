"""Run one program on many inputs, each in a fresh namespace, and print one JSON
line: per input, its observable outcome, whether it passes, and (if asked) the
lines of the program it executed.  python3 child.py PAYLOAD.json"""
import contextlib, io, json, os, signal, sys, tempfile
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../../../src/runner"))
from _values import decode, encode            # noqa: E402
from _child import _eq, _stdout_eq, _make_stdin  # noqa: E402
sys.setrecursionlimit(20000)


class _Timeout(Exception):
    pass


def _alarm(*_):
    raise _Timeout()


def run(p):
    mode, entry, tol, per = p["mode"], p.get("entry"), p["tol"], p["per_test"]
    try:
        code = compile(p["src"], "<candidate>", "exec")
        pre = compile(p.get("prelude") or "", "<prelude>", "exec")
    except BaseException as e:
        return {"error": f"{type(e).__name__}: {e}"}
    signal.signal(signal.SIGALRM, _alarm)
    real_stdin, cwd0, out = sys.stdin, os.getcwd(), []
    lines = set()
    mon = sys.monitoring
    if p["trace"]:          # each line of the program is recorded once per input, then disabled
        def on_line(c, line):
            if c.co_filename == "<candidate>":
                lines.add(line)
            return mon.DISABLE
        mon.use_tool_id(3, "footprint")
        mon.register_callback(3, mon.events.LINE, on_line)
    for t in p["inputs"]:
        lines.clear()
        if p["trace"]:
            mon.restart_events()
        buf, res, got = io.StringIO(), {}, None
        if mode != "call":
            sys.stdin = _make_stdin(t.get("stdin", ""))
        if mode == "file":
            d = tempfile.mkdtemp()
            open(os.path.join(d, "input.txt"), "w").write(t.get("stdin", ""))
            os.chdir(d)
        signal.setitimer(signal.ITIMER_REAL, per)
        if p["trace"]:
            mon.set_events(3, mon.events.LINE)
        try:
            with contextlib.redirect_stdout(buf):
                ns = {"__name__": "__main__"}
                if mode == "call":
                    exec(pre, ns)
                    ns["__name__"] = "__candidate__"
                exec(code, ns)
                if mode == "call":
                    got = ns[t.get("entry", entry)](*decode(t.get("args", [])))
                    res["r"] = encode(got)
        except SystemExit:
            pass
        except _Timeout:
            res["t"] = 1
        except RecursionError:
            res["e"] = "RecursionError"
        except BaseException as e:
            res["e"] = f"{type(e).__name__}: {e}"
        finally:
            if p["trace"]:
                mon.set_events(3, 0)
            signal.setitimer(signal.ITIMER_REAL, 0)
            sys.stdin = real_stdin
        s = buf.getvalue()
        if mode == "file":
            o = os.path.join(os.getcwd(), "output.txt")
            if os.path.exists(o):
                s = open(o).read()
            os.chdir(cwd0)
        res["s"] = s
        if "t" in res or "e" in res:
            ok = False
        elif mode == "call":
            ok = _eq(got, decode(t.get("expected")), tol)
        else:
            ok = _stdout_eq(s, t.get("expected", ""), tol)
        rec = {"o": json.dumps(res, sort_keys=True, default=str), "ok": bool(ok)}
        if p["trace"]:
            rec["L"] = sorted(lines)
        out.append(rec)
    return {"runs": out}


if __name__ == "__main__":
    print(json.dumps(run(json.load(open(sys.argv[1])))))
