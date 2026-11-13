"""The language's checks as a filter on Python rules: what build_filter.py rejects in the build loop
and run_filter.py drops at repair time. A rule is rejected if, on a program of the build set, it
raises or runs past the limit, its replacement equals the matched code (the language's T != P), or a
candidate reads a name nothing binds that the program did not (Tmpl, and Definition 3.4(b)).
    python3 results/checks/python_rules/filter/common.py   runs its own check"""
import ast, builtins, importlib.util, signal, sys
from pathlib import Path
ROOT, HERE = Path(__file__).resolve().parents[4], Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT), str(HERE.parent)]
import rewrite                                     # noqa: E402
sys.modules["src.core.rewrite"] = rewrite
from src.core.repair import Rule                   # noqa: E402
BI = set(dir(builtins))
LIMIT = 2.0                                        # the engine's limit per application


def unbound(src):
    """Names the program reads that no scope binds; None if it does not parse."""
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


def check(r, programs):
    """The first reason to reject the Rewrite r on the programs, or None."""
    for src in programs:
        tree = ast.parse(src)
        ctx, outside, base = rewrite.Ctx(src, tree), {}, unbound(src) or set()
        for node in ast.walk(tree):
            if not isinstance(node, (ast.expr, ast.stmt)) or isinstance(node, rewrite._DEFS):
                continue
            signal.signal(signal.SIGALRM, _alarm)
            signal.setitimer(signal.ITIMER_REAL, LIMIT)
            try:
                if not r.match(node, ctx):
                    continue
                texts = r.replace(node, ctx)
            except _Stop:
                return f"{r.name}: ran past the time limit"
            except Exception as e:                 # noqa: BLE001 - this is what the filter looks for
                return f"{r.name}: raised {type(e).__name__}: {str(e)[:80]}"
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            for t in ([texts] if isinstance(texts, str) else list(texts or [])):
                if not isinstance(t, str):
                    continue
                if t.strip() == ctx.text(node).strip():
                    return f"{r.name}: a rewrite equal to its match changes nothing"
                cand = rewrite.substitute(src, tree, ctx, node, t, outside)
                if cand is not None and cand != src:
                    new = (unbound(cand) or set()) - base
                    if new:
                        return (f"{r.name}: replacement names {sorted(new)} come from neither the match nor "
                                "builtins; take them from the matched code")
    return None


def rewrites(path):
    """The Rewrites of a fixer.py."""
    spec = importlib.util.spec_from_file_location("_tool_fixer", path)
    m = importlib.util.module_from_spec(spec)
    m.__dict__.setdefault("Rule", Rule)
    spec.loader.exec_module(m)
    got = m.Fixer().rules()
    if not isinstance(got, list) or not all(isinstance(r, rewrite.Rewrite) for r in got):
        raise TypeError("every rule must be a Rewrite; Fixer().rules() returned something else")
    return got


def guarded(r):
    """r as a Rule that drops the candidates reading a name nothing binds, as Definition 3.4(b) does."""
    def apply(src):
        base = unbound(src) or set()
        return [c for c in r.apply(src) if not ((unbound(c) or set()) - base)]
    return Rule(name=r.name, apply=apply, symptoms=tuple(r.symptoms), local=True)


if __name__ == "__main__":
    R = rewrite.Rewrite
    src = "def f(day):\n    return day + 1\n"
    name = lambda n, c: isinstance(n, ast.Name) and n.id == "day" and isinstance(n.ctx, ast.Load)
    invent = R("invent", name, lambda n, c: "date")
    same = R("same", name, lambda n, c: "day")
    boom = R("boom", name, lambda n, c: {}["x"])
    good = R("good", lambda n, c: isinstance(n, ast.Constant), lambda n, c: "2")
    assert "neither the match" in check(invent, [src]), check(invent, [src])
    assert "changes nothing" in check(same, [src])
    assert "raised KeyError" in check(boom, [src])
    assert check(good, [src]) is None
    assert guarded(invent)(src) == [] and guarded(good)(src) == ["def f(day):\n    return day + 2\n"]
    print("filter ok")
