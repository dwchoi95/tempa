"""What the same builders' rules do when they are Python functions, against the rule language:
every rule of the three builds applied once to every buggy program, in-process, no test run.
Per application of a Python rule: a match or replace function that raised (the engine swallows
it and the rule abstains at that node), a replacement text the engine refused (does not parse
or does not fit the hole), and a run past the time limit. Per candidate, for both forms: names
it reads that nothing binds. Per rule: applications with any candidate, repairs logged.
    python3 -I audit.py REPO   -> audit.txt, audit.json"""
import ast, builtins, json, signal, sys, time
from collections import Counter, defaultdict
from multiprocessing import Pool
from pathlib import Path
REPO = Path(sys.argv[1]); HERE = REPO / "results/checks/python_rules"
sys.path[:0] = [str(REPO), str(HERE)]
import rewrite                                     # noqa: E402
sys.modules["src.core.rewrite"] = rewrite
from src.core.rulelang import compile_rules        # noqa: E402
from src.experiments._common import ORDER          # noqa: E402
import importlib.util                              # noqa: E402
M = ("claude-sonnet-5", "gpt-5.4-mini")
BI = set(dir(builtins))


def unbound(src):
    """Names the program reads that no scope binds: a NameError waiting on the path that reads them."""
    try:
        t = ast.parse(src)
    except SyntaxError:
        return None
    bound = set()
    for n in ast.walk(t):
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            bound.add(n.id)
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(n.name)
        elif isinstance(n, ast.arg):
            bound.add(n.arg)
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            bound.update((a.asname or a.name).split(".")[0] for a in n.names)
        elif isinstance(n, ast.ExceptHandler) and n.name:
            bound.add(n.name)
    return {n.id for n in ast.walk(t) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)} - bound - BI


class _Stop(Exception):
    pass


def _alarm(*_):
    raise _Stop


def py_rules(d):
    def module(f):
        s = importlib.util.spec_from_file_location("_t_" + f.stem, f)
        m = importlib.util.module_from_spec(s)
        s.loader.exec_module(m)
        return m
    return [r for r in module(d / "fixer.py").Fixer().rules() if isinstance(r, rewrite.Rewrite)]


def py_apply(rule, source, c):
    """Rewrite.apply with its silent paths counted."""
    tree = ast.parse(source)
    ctx = rewrite.Ctx(source, tree)
    outside, out = {}, []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.expr, ast.stmt)) or isinstance(node, rewrite._DEFS):
            continue
        try:
            if not rule.match(node, ctx):
                continue
            texts = rule.replace(node, ctx)
        except _Stop:
            raise
        except Exception as e:                     # noqa: BLE001
            c["raised"] += 1
            c["raised:" + type(e).__name__] += 1
            continue
        c["matched"] += 1
        for t in ([texts] if isinstance(texts, str) else list(texts or [])):
            if not isinstance(t, str):
                c["not_text"] += 1
                continue
            cand = rewrite.substitute(source, tree, ctx, node, t, outside)
            if cand is None:
                c["refused"] += 1
            elif cand != source and cand not in out:
                out.append(cand)
    return out


def job(a):
    build, pid, m = a
    root = REPO / ("benchmark" if build == "r0" else f"rebuild_work/{build}") / pid / "buggy"
    progs = [f.read_text() for f in sorted(root.glob("*.py"))]
    res = {}
    lang = (REPO / ("tools" if build == "r0" else f"tools/rebuild/{build}") / pid / m / "fixer.rules").read_text()
    lr, _ = compile_rules(lang)
    py = py_rules(HERE / "tools_python" / build / pid / m)
    for form, rules in (("python", py), ("language", lr)):
        c = Counter(); fired = set(); t0 = time.time()
        c["rules"] = len(rules)
        for p in progs:
            try:
                base = unbound(p) or set()
            except Exception:
                continue
            for r in rules:
                c["applications"] += 1
                signal.signal(signal.SIGALRM, _alarm); signal.setitimer(signal.ITIMER_REAL, 2.0)
                try:
                    out = py_apply(r, p, c) if form == "python" else r.apply(p)
                except _Stop:
                    c["timeout"] += 1; out = []
                except SyntaxError:
                    out = []
                except Exception as e:             # noqa: BLE001
                    c["crash"] += 1; c["crash:" + type(e).__name__] += 1; out = []
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
                if out:
                    fired.add(r.name)
                c["candidates"] += len(out)
                for q in out:
                    u = unbound(q)
                    if u is None:
                        c["cand_syntax"] += 1
                    elif u - base:
                        c["cand_unbound"] += 1
        c["fired_rules"] = len(fired); c["seconds"] = round(time.time() - t0)
        res[form] = dict(c)
    return (build, pid, m, res)


if __name__ == "__main__":
    jobs = [(b, p, m) for b in ("r0", "r1", "r2") for p in ORDER for m in M]
    with Pool(2) as pool:
        rs = pool.map(job, jobs, chunksize=1)
    (HERE / "audit.json").write_text(json.dumps(rs))
    tot = defaultdict(Counter)
    for b, p, m, r in rs:
        for form, c in r.items():
            tot[(m, form)].update(c); tot[("all", form)].update(c)
    out = []
    for k in sorted(tot):
        out.append(f"{k}: " + " ".join(f"{a}={v}" for a, v in sorted(tot[k].items())))
    print("\n".join(out)); (HERE / "audit.txt").write_text("\n".join(out) + "\n")
