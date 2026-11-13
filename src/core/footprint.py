"""The semantic footprint of an edit: the places of ``p`` that its execution must
reach before ``q`` can behave differently (the paper's Theorem on footprints).

An edit is local in its syntax but not always in its meaning. In Python, one
assignment makes a name local to its whole function, and one ``yield`` makes the
whole function a generator. The footprint therefore holds:

* the edited sites, the maximal subtrees of ``p`` at which ``p`` and ``q`` differ,
  or, for an inserted statement, the statement it is inserted before;
* every occurrence of a name whose classification (parameter, local, global,
  free) changes in a scope; and
* if a function changes its kind (plain, generator, coroutine, or asynchronous
  generator), the whole program, since its callers lie anywhere.
"""
from __future__ import annotations

import ast
import collections
import difflib
import functools
import symtable

_FUNCS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
_FOLDED = (ast.ListComp, ast.SetComp, ast.DictComp)
_SCOPES = _FUNCS + _FOLDED + (ast.GeneratorExp,)


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


def _ends(x: list, y: list, key) -> list:
    """The pairs of two lists that correspond: their common ends, like statements, and what still matches between."""
    i = 0
    while i < min(len(x), len(y)) and key(x[i]) == key(y[i]):
        i += 1
    j = 0
    while j < min(len(x), len(y)) - i and key(x[-1 - j]) == key(y[-1 - j]):
        j += 1
    u, v = x[i:len(x) - j], y[i:len(y) - j]
    mid = difflib.SequenceMatcher(None, [key(e) for e in u], [key(e) for e in v], autojunk=False)
    pairs = [*zip(x[:i], y[:i]), *((u[m.a + k], v[m.b + k]) for m in mid.get_matching_blocks() for k in range(m.size)),
             *zip(x[len(x) - j:], y[len(y) - j:])]
    if len(x) != len(y):                               # with another count, those of a repeated name may be any of each other
        n = collections.Counter(map(key, x)) | collections.Counter(map(key, y))
        pairs += [(a, b) for a in x for b in y if key(a) == key(b) and n[key(a)] > 1]
    return pairs


def _pairs(a, b):
    """The scopes of two symbol tables that correspond."""
    yield a, b
    for c, d in _ends(a.get_children(), b.get_children(), lambda t: (t.get_type(), t.get_name())):
        yield from _pairs(c, d)


def _class(s) -> tuple:
    return (s.is_parameter(), s.is_local(), s.is_global(), s.is_declared_global(), s.is_free(), s.is_nonlocal())


# A class body stores these before and after its own code, reading __name__, though the symbol
# tables list them only when the body names them; a global or nonlocal declaration redirects them.
_CLASS_IMPLICIT = {"__module__": (False, True, False, False, False, False),
                   "__qualname__": (False, True, False, False, False, False),
                   "__firstlineno__": (False, True, False, False, False, False),
                   "__static_attributes__": (False, True, False, False, False, False),
                   "__name__": (False, False, True, False, False, False)}


def _outer(n: ast.AST) -> list:
    """What a function or class node evaluates in the scope around it."""
    a = getattr(n, "args", None)
    return [*getattr(n, "decorator_list", ()), *getattr(n, "bases", ()), *(k.value for k in getattr(n, "keywords", ())),
            *(a.defaults if a else ()), *(d for d in (a.kw_defaults if a else ()) if d),
            *(p.annotation for p in (ast.walk(a) if a else ()) if isinstance(p, ast.arg) and p.annotation),
            *((n.returns,) if getattr(n, "returns", None) else ())]


def _own(n: ast.AST):
    """n and what runs in its scope; a nested function or class stands for itself and what it
    evaluates outside. A comprehension's only yield can be in what its scope around evaluates."""
    yield n
    for c in _outer(n) if isinstance(n, _FUNCS) else ast.iter_child_nodes(n):
        yield from _own(c)


def _async_gen(n: ast.GeneratorExp) -> bool:
    """A generator expression is asynchronous if it iterates asynchronously or suspends in its own
    scope: an await, or an asynchronous comprehension, in its element, conditions, or later
    iterables. Its leftmost iterable belongs to the scope around it, and so does that of a
    generator expression nested in it."""
    def suspends(x):
        if isinstance(x, ast.GeneratorExp):
            return suspends(x.generators[0].iter)
        if isinstance(x, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return False
        if isinstance(x, ast.Await) or isinstance(x, _FOLDED) and any(g.is_async for g in x.generators):
            return True
        return any(suspends(c) for c in ast.iter_child_nodes(x))
    return any(g.is_async for g in n.generators) or any(
        suspends(x) for x in [n.elt, *(c for g in n.generators for c in g.ifs), *(g.iter for g in n.generators[1:])])


def _kinds(roots: list) -> list:
    """[(name, kind, the functions and classes inside it)] for those directly under roots, in
    source order. A kind is (async, yields): plain, generator, coroutine, or asynchronous
    generator; a generator expression counts as a function."""
    out = []
    for m in (m for r in roots for m in _own(r) if isinstance(m, _FUNCS + (ast.GeneratorExp,))):
        if isinstance(m, ast.GeneratorExp):
            out.append(("<genexpr>", (_async_gen(m), True), []))
            continue
        body = m.body if isinstance(m.body, list) else [m.body]
        out.append((getattr(m, "name", "<lambda>"), (isinstance(m, ast.AsyncFunctionDef), any(
            isinstance(x, (ast.Yield, ast.YieldFrom)) for b in body for x in _own(b))), _kinds(body)))
    return out


def _kind_changes(x: list, y: list) -> bool:
    return any(a[1] != b[1] or _kind_changes(a[2], b[2]) for a, b in _ends(x, y, lambda e: e[0]))


def _mentions(node: ast.AST, name: str):
    names = {name, name[name.find("__"):]} if name.startswith("_") and "__" in name else {name}   # the tables mangle, the tree does not
    for m in ast.walk(node):
        if (isinstance(m, ast.Name) and m.id in names or isinstance(m, ast.arg) and m.arg in names
                or isinstance(m, (ast.Global, ast.Nonlocal)) and names & set(m.names)
                or isinstance(m, (ast.ExceptHandler, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and m.name in names
                or isinstance(m, ast.alias) and (m.asname or m.name).split(".")[0] in names
                or isinstance(m, ast.ClassDef) and names & _CLASS_IMPLICIT.keys()      # its implicit stores
                or isinstance(m, (ast.MatchAs, ast.MatchStar)) and m.name in names
                or isinstance(m, ast.MatchMapping) and m.rest in names
                or "__class__" in names and isinstance(m, ast.Call) and isinstance(m.func, ast.Name)
                and m.func.id == "super" and not m.args and not m.keywords):   # a bare super() reads __class__
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
        if isinstance(n, _SCOPES):
            owners.setdefault(n.lineno, []).append(n)
    parent = {c: n for n in ast.walk(tp) for c in ast.iter_child_nodes(n)}
    return tp, symtable.symtable(p, "<p>", "exec"), owners, _kinds(tp.body), parent


def _targets(c: ast.AST) -> set:
    return {m.id for g in c.generators for m in ast.walk(g.target) if isinstance(m, ast.Name) and isinstance(m.ctx, ast.Store)}


def _folded(tp: ast.AST, tq: ast.AST):
    """(comprehension of p, name) for every name it binds, or its counterpart in q binds, but not both. Since 3.12
    the symbol tables fold these comprehensions into the scope around them, so only the trees tell."""
    x, y = ([n for n in ast.walk(t) if isinstance(n, _FOLDED)] for t in (tp, tq))
    i = 0
    while i < min(len(x), len(y)) and _key(x[i]) == _key(y[i]):
        i += 1
    j = 0
    while j < min(len(x), len(y)) - i and _key(x[-1 - j]) == _key(y[-1 - j]):
        j += 1
    x, y = x[i:len(x) - j], y[i:len(y) - j]
    for k, c in enumerate(x):                          # with another count, which becomes which is unknown
        for name in _targets(c) ^ _targets(y[k]) if len(x) == len(y) else _targets(c).union(*map(_targets, y)):
            yield [c], name


def rescoped(p: str, q: str):
    """(the nodes of p that are the scope, name) for every name a scope classifies differently in q."""
    tp, sp, owners, _, _ = _side(p)
    yield from _folded(tp, ast.parse(q))
    for a, b in _pairs(sp, symtable.symtable(q, "<q>", "exec")):
        names = {s.get_name(): _class(s) for s in b.get_symbols()}
        scope = owners.get(a.get_lineno()) or [tp]
        for s in a.get_symbols():
            if s.get_name() in names and names[s.get_name()] != _class(s):
                yield [tp] if a.get_type() == "module" else scope, s.get_name()
        if a.get_type() == "class":
            mine = {s.get_name(): _class(s) for s in a.get_symbols()}
            for x, default in _CLASS_IMPLICIT.items():
                if mine.get(x, default) != names.get(x, default) and not (x in mine and x in names):
                    yield scope, x


def _footprint(p: str, q: str, sites_only: bool = False):
    tp, _, _, kp, _ = _side(p)
    tq = ast.parse(q)
    nodes: list[ast.AST] = []
    _sites(tp, tq, tp, nodes)
    if sites_only:
        return tp, nodes, False
    for scope, x in rescoped(p, q):
        for o in scope:
            nodes.extend(_mentions(o, x))
    return tp, nodes, _kind_changes(kp, _kinds(tq.body))


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
        if isinstance(n, ast.Constant) and isinstance(parent.get(n), ast.Expr):
            n = parent[n]
        if isinstance(n, ast.Pass) or isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant):
            par = parent.get(n)
            sib = next((getattr(par, f) for f in par._fields
                        if isinstance(getattr(par, f, None), list) and n in getattr(par, f)), [])
            i = sib.index(n)
            n = sib[i + 1] if i + 1 < len(sib) else par
        if isinstance(n, ast.arg):                     # no step evaluates a parameter; its def does
            lines.add(parent[parent[n]].lineno)
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
    d = "def f():\n    if False:\n        g = lambda x=0: 0\n    return 1\n"             # a default runs in f
    assert footprint_lines(d, d.replace("x=0", "x=(yield 0)")) is None
    assert footprint_lines("f = lambda: (1 if True else\n    0)\n", "f = lambda: (1 if True else\n    (yield 0))\n") is None
    n = "x = 0\ndef u():\n    global x\ndef f():\n    if False:\n        global x\n    def x():\n        return 1\n"
    assert 7 in footprint_lines(n, n.replace("        global x", "        pass"))      # a def binds its name
    s2 = "def h():\n    return 1\ndef h():\n    return 2\n"                          # same-named functions count apart
    assert footprint_lines(s2, s2.replace("return 1", "yield 1")) is None
    b6 = "def f():\n    x = 0\n    return [\n        x\n        for z in (0,)\n        if x\n        for y in ()\n    ]\n"
    assert footprint_lines(b6, b6.replace("for y", "for x")) == {4, 6, 7}  # the folded tables do not show this rescoping
    assert footprint_lines(b6, b6.replace("if x", "if z")) == {6}
    b7 = b6.replace("for y in ()", "for x in ()")
    assert {4, 6} <= footprint_lines(b7, b7.replace("for x in ()", "for y in [0 for x in ()]"))   # an inner x must not mask the outer
    b11 = "def f(a):\n    i = 0\n    r = [[0 for j in a] for i in a]\n    return i\n"
    assert footprint_lines(b11, b11.replace("for j in a", "for j in a + a")) == {3}   # nesting alone rescopes nothing
    b8 = ("x = 1\nif False:\n    def a(): return 0\ndef f():\n    if False:\n        x == 2\n    return x\n"
          "if False:\n    def b(): return 0\nprint(f() == 1)\n")
    c8 = b8.replace("def a", "def aa").replace("def b", "def bb")
    assert 7 in footprint_lines(b8, c8.replace("x == 2", "x = 2"))         # a scope between two changed siblings
    assert footprint_lines(b8, c8.replace("x == 2", "yield 0")) is None
    b9 = "_C__x = 1\nclass C:\n    def f():\n        if False:\n            __x == 2\n        return __x\n    print(f())\n"
    assert 6 in footprint_lines(b9, b9.replace("__x == 2", "__x = 2"))     # a mangled name
    b10 = "def f(x,\n      y):\n    return 0\nprint(f(1, 2))\n"
    assert 1 in footprint_lines(b10, "def f(x):\n    return 0\nprint(f(1, 2))\n")   # a parameter counts at the function
    b12 = "x = 1\nif False:\n    a = (x for y in ())\nr = (\n    x\n    for y in (0,)\n    if x\n    for x in ()\n)\nprint(list(r))\n"
    c12 = b12.replace("for x in ()", "for z in ()").replace("a = (x for y in ())\n", "a = (x for y in ())\n    b = (x for y in () for x in ())\n")
    assert 7 in footprint_lines(b12, c12)                                  # a repeated scope name
    b13 = "x = 1\nif False:\n    def f(): return x\ndef f():\n    if False:\n        x == 2\n    return x\nprint(f() == 1)\n"
    c13 = b13.replace("def f(): return x\n", "def f(): return x\n    def f(): return x\n", 1)
    assert footprint_lines(b13, c13.replace("x == 2", "yield 0")) is None
    b14 = "_C__x = 1\ndef f():\n    if False:\n        _C__x == 2\n    return _C__x\nprint(f())\n"
    assert 5 in footprint_lines(b14, b14.replace("_C__x == 2", "_C__x = 2"))
    b15 = "def f():\n    if False:\n        def g(x: int): pass\n    return 1\nprint(f() == 1)\n"
    assert footprint_lines(b15, b15.replace("x: int", "x: (yield 0)")) is None
    b16 = 'def f():\n    "hello"\n    return 1\nprint(f())\n'
    assert footprint_lines(b16, b16.replace('"hello"', 'print("hello")')) == {3}   # the string compiles to nothing
    assert footprint_lines("async def f():\n    yield 1\n", "async def f():\n    return 1\n") is None   # kinds: (async, yields)
    assert footprint_lines("def f():\n    yield 1\n", "async def f():\n    yield 1\n") is None
    assert footprint_lines("async def f():\n    x = 1\n    return x\n",
                           "async def f():\n    x = await g()\n    return x\n") == {2}           # await keeps the kind
    assert footprint_lines("async def f(a):\n    return (x for x in a)\n",
                           "async def f(a):\n    return (await x for x in a)\n") is None     # an asynchronous genexp
    b19 = "import asyncio\nasync def v():\n    return (1,)\nasync def f():\n    return (\n        x\n        for x in await v()\n    )\n"
    assert footprint_lines(b19, b19.replace("        x\n", "        await x\n")) is None   # its first iterable is not its own
    b20 = "async def f():\n    return (\n        [x for x in ()]\n        for y in (0,)\n    )\n"
    assert footprint_lines(b20, b20.replace("[x for", "[x async for")) is None   # an async comprehension awaits
    b17 = "class C(A):\n    def f(self):\n        pass\n        return super().f()\n"
    assert 4 in footprint_lines(b17, b17.replace("pass", "__class__ = 1"))           # a bare super() reads __class__
    b18 = "x = 0\ndef f(v):\n    pass\n    match v:\n        case [x]:\n            return x\n    return x\n"
    assert {5, 6, 7} <= footprint_lines(b18, b18.replace("pass", "global x"))        # a capture binds
    b21 = "class C:\n    if False:\n        pass\nprint(__qualname__)\n"
    assert 1 in footprint_lines(b21, b21.replace("pass", "global __qualname__"))   # the class body's own store moves
    print("footprint ok")
