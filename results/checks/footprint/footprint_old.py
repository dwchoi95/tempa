"""The semantic footprint of an edit: the places of ``p`` that its execution must
reach before ``q`` can behave differently (the paper's Theorem on footprints).

An edit is local in its syntax but not always in its meaning. In Python, one
assignment makes a name local to its whole function, and one ``yield`` makes the
whole function a generator. The footprint therefore holds:

* the edited sites, the maximal subtrees of ``p`` at which ``p`` and ``q`` differ,
  or, for an inserted statement, the statement it is inserted before;
* every occurrence of a name whose classification (parameter, local, global,
  free) changes in a scope; and
* if a function changes its kind (generator or not), the whole program, since
  its callers lie anywhere.
"""
from __future__ import annotations

import ast
import functools
import symtable

_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
           ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)


def _key(x):
    return ast.dump(x) if isinstance(x, ast.AST) else (type(x).__name__, repr(x))   # False is not 0


def _sites(a: ast.AST, b: ast.AST, anc: ast.AST, out: list) -> None:
    """Append to ``out`` the maximal subtrees of ``a`` (in p) that differ from ``b``
    (in q); ``anc`` is the nearest ancestor of ``a`` that has a source position."""
    if hasattr(a, "lineno"):
        anc = a
    if type(a) is not type(b):
        out.append(anc)
        return
    for f in a._fields:
        x, y = getattr(a, f, None), getattr(b, f, None)
        if isinstance(x, list) and isinstance(y, list):
            if [_key(e) for e in x] == [_key(e) for e in y]:
                continue
            if len(x) == len(y):
                for e, g in zip(x, y):
                    if isinstance(e, ast.AST) and isinstance(g, ast.AST):
                        _sites(e, g, anc, out)
                    elif e != g:
                        out.append(anc)
                        return
                continue
            i = 0
            while i < min(len(x), len(y)) and _key(x[i]) == _key(y[i]):
                i += 1
            j = 0
            while j < min(len(x), len(y)) - i and _key(x[-1 - j]) == _key(y[-1 - j]):
                j += 1
            mid = x[i:len(x) - j]
            if mid and all(hasattr(e, "lineno") for e in mid):
                out.extend(mid)
            elif not mid and x and isinstance(x[0], ast.stmt):
                out.append(x[min(i, len(x) - 1)])      # the statement it is inserted before
            else:
                out.append(anc)
        elif isinstance(x, ast.AST) and isinstance(y, ast.AST):
            _sites(x, y, anc, out)
        elif _key(x) != _key(y):
            out.append(anc)
            return


def _classes(src: str) -> dict:
    """{scope path: (lineno, {name: classification})} over p's symbol tables."""
    out = {}

    def walk(t, path):
        k, n = path + ((t.get_type(), t.get_name()),), 0
        while k in out:
            n += 1
            k = path + ((t.get_type(), t.get_name(), n),)
        out[k] = (t.get_lineno(), {s.get_name(): (s.is_parameter(), s.is_local(), s.is_global(),
                                                  s.is_declared_global(), s.is_free(), s.is_nonlocal())
                                   for s in t.get_symbols()})
        for c in t.get_children():
            walk(c, k)
    walk(symtable.symtable(src, "<p>", "exec"), ())
    return out


def _kinds(tree: ast.AST) -> dict:
    """{function name: is a generator or coroutine}, nested functions by dotted path."""
    out = {}

    def own(fn):
        st = list(ast.iter_child_nodes(fn))
        while st:
            m = st.pop()
            if isinstance(m, _SCOPES):
                continue
            yield m
            st.extend(ast.iter_child_nodes(m))

    def walk(n, path):
        for c in ast.iter_child_nodes(n):
            if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef)):
                p = path + (c.name,)
                out[p] = isinstance(c, ast.AsyncFunctionDef) or any(
                    isinstance(m, (ast.Yield, ast.YieldFrom, ast.Await)) for m in own(c))
                walk(c, p)
            else:
                walk(c, path)
    walk(tree, ())
    return out


def _mentions(node: ast.AST, name: str):
    for m in ast.walk(node):
        if (isinstance(m, ast.Name) and m.id == name or isinstance(m, ast.arg) and m.arg == name
                or isinstance(m, (ast.Global, ast.Nonlocal)) and name in m.names
                or isinstance(m, ast.ExceptHandler) and m.name == name
                or isinstance(m, ast.alias) and (m.asname or m.name).split(".")[0] == name):
            yield m


def footprint(p: str, q: str) -> tuple[list[ast.AST], bool]:
    """(the nodes of p in the footprint of the edit p -> q, whether it is the whole
    program because a function changed its kind)."""
    return _footprint(p, q)[1:]


@functools.lru_cache(maxsize=64)
def _side(p: str):
    """What the footprint needs of p alone, computed once per p since a search
    compares one buggy program with many candidates (never mutated)."""
    tp = ast.parse(p)
    owners = {}
    for n in ast.walk(tp):
        if isinstance(n, _SCOPES) or isinstance(n, ast.Module):
            owners.setdefault(getattr(n, "lineno", 0), []).append(n)
    parent = {c: n for n in ast.walk(tp) for c in ast.iter_child_nodes(n)}
    return tp, _classes(p), owners, _kinds(tp), parent


def _footprint(p: str, q: str, sites_only: bool = False):
    tp, cp, owners, kp, _ = _side(p)
    tq = ast.parse(q)
    nodes: list[ast.AST] = []
    _sites(tp, tq, tp, nodes)
    if sites_only:
        return tp, nodes, False
    cq = _classes(q)
    for path, (line, names) in cp.items():
        if path not in cq:
            continue
        changed = [x for x, c in names.items() if x in cq[path][1] and cq[path][1][x] != c]
        for x in changed:
            scope = tp if len(path) == 1 else None
            for o in owners.get(line, []):
                if not isinstance(o, ast.Module):
                    scope = o
                    break
            nodes.extend(_mentions(scope or tp, x))
    kq = _kinds(tq)
    whole = any(k in kq and kq[k] != v for k, v in kp.items())
    return tp, nodes, whole


def footprint_lines(p: str, q: str, sites_only: bool = False) -> set[int] | None:
    """The source lines of p that the footprint covers, as a line trace observes
    them; None for the whole program. ``sites_only`` takes the edited sites alone,
    as the effect theorem allows for an edit made by scope-neutral rules. A statement that compiles to no instruction
    (a docstring or ``pass``) never shows in a trace, so the statement after it, or
    the enclosing one if it ends its block, stands in for it."""
    tp, nodes, whole = _footprint(p, q, sites_only)
    if whole:
        return None
    parent = _side(p)[4]
    lines = set()
    for n in nodes:
        if isinstance(n, ast.Pass) or isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant):
            par = parent.get(n)
            sib = next((getattr(par, f) for f in par._fields
                        if isinstance(getattr(par, f, None), list) and n in getattr(par, f)), [])
            i = sib.index(n)
            n = sib[i + 1] if i + 1 < len(sib) else par
        if hasattr(n, "lineno"):
            lines.update(range(n.lineno, (n.end_lineno or n.lineno) + 1))
    return lines


def hint(p: str, q: str, neutral: bool = False) -> str:
    """The hint a repair of ``p`` into ``q`` comes with: the lines of its footprint.
    Every input on which the repair changes the outcome runs through one of them
    (the paper's Theorem on footprints); ``neutral``, for a repair by scope-neutral
    rules alone, takes the edited sites without analyzing any scope."""
    sites = footprint_lines(p, q, sites_only=True)
    lines = sites if neutral else footprint_lines(p, q)
    if lines is None:
        return "the whole program: a function changed its kind"
    extra = sorted(lines - sites)
    return f"lines {sorted(lines)}" + (f", {extra} change meaning unedited" if extra else "")


if __name__ == "__main__":
    b = "def f(xs):\n    out == []\n    for x in xs:\n        out.append(x)\n    return out\n"
    c = "def f(xs):\n    out = []\n    for x in xs:\n        out.append(x)\n    return out\n"
    assert footprint_lines(b, c) == {2, 4, 5}, footprint_lines(b, c)     # `out` turns local in f
    assert hint(b, c) == "lines [2, 4, 5], [4, 5] change meaning unedited", hint(b, c)
    b2 = "def g(n):\n    if n < 0:\n        return 0\n    return n + 1\n"
    c2 = "def g(n):\n    if n <= 0:\n        return 0\n    return n + 1\n"
    assert footprint_lines(b2, c2) == {2}
    c3 = "def g(n):\n    if n < 0:\n        return 0\n    s = 1\n    return n + 1\n"
    assert footprint_lines(b2, c3) == {4}                                  # inserted before line 4
    c4 = "def g(n):\n    if n < 0:\n        yield 0\n    return n + 1\n"
    assert footprint_lines(b2, c4) is None                                 # g turns a generator
    assert hint(b2, c2, neutral=True) == hint(b2, c2) == "lines [2]"
    assert hint(b2, c4).startswith("the whole program")
    assert footprint_lines("def h():\n    return False\n", "def h():\n    return 0\n") == {2}
    b5 = 'def k(s):\n    """doc"""\n    return s\n'
    assert footprint_lines(b5, "def k(s):\n    if not s:\n        return 0\n    return s\n") == {3}
    print("footprint ok")
