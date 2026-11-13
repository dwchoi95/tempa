"""The rule language: one-hole rewrite rules as data (Section 3.2).

A builder writes rules in this language, and the engine interprets them; no
builder-written code runs. A rule names a pattern over Python's syntax with
metavariables, an optional guard, and templates:

    rule rest_isupper_to_equality_form
    symptoms: wrong
    match: $X.isupper()
    where: match($X, "$W[1:]") or match($X, "$W[1:len($_)]")
    rewrite: $X.upper() == $X

Metavariables are ``$X`` or ``$X:Sort`` with Sort one of Expr (the default),
Name, Int, Str, Const, Attr, Stmt, Stmts, Cmp, Arith, Bool (the last three are
operators); ``$*X`` matches a run of list elements and ``$_`` (or a bare ``_``
in a pattern) anything. A match of two or three statements makes the hole a
run of statements. The guard is a boolean formula over the primitives of
``_PRIMS``; the context primitives (``field``, ``parent``, ``inside``, ``first``,
``last``, ``prev``, ``next``, ``before``, ``after``) speak of where the hole
sits, ``inside`` binding the nearest enclosing for/while/if/def (never across
a def boundary). Templates are Python with the metavariables, and
``${t[$k]}`` looks a binding's text up in a table ``table t: {...}``.

What the language guarantees, for every rule a builder writes (Section 3.2):
matching, guard evaluation and instantiation always terminate and are
deterministic; an application changes one site; a template mentions only
names the match bound, the pattern's own names, builtins, and names it binds
itself, renamed apart from the program's; and a rule is a function of the
program alone. ``compile_rules`` rejects at build time what violates the
static semantics, with a reason the build loop returns to the builder.
"""
from __future__ import annotations

import ast
import builtins
import copy
import re
import textwrap
from dataclasses import dataclass, field

from src.core.repair import Rule
from footprint_old import _kinds
from src.core.rewrite import Ctx, _DEFS, _dump, _holed, _path, substitute

SORTS = ("Expr", "Name", "Int", "Str", "Const", "Attr", "Stmt", "Stmts", "Cmp", "Arith", "Bool")
_OPS = {"Cmp": "<", "Arith": "+", "Bool": "and"}          # placeholder token per operator sort
_TOK = {ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=", ast.Eq: "==", ast.NotEq: "!=",
        ast.In: "in", ast.NotIn: "not in", ast.Is: "is", ast.IsNot: "is not",
        ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/", ast.FloorDiv: "//", ast.Mod: "%",
        ast.Pow: "**", ast.MatMult: "@", ast.LShift: "<<", ast.RShift: ">>", ast.BitOr: "|",
        ast.BitXor: "^", ast.BitAnd: "&", ast.And: "and", ast.Or: "or"}
_FAMILY = {"Cmp": ast.cmpop, "Arith": ast.operator, "Bool": ast.boolop}
_MV = re.compile(r"\$(\*?)([A-Za-z_][A-Za-z0-9_]*)(?::([A-Za-z]+))?")
_TB = re.compile(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\[\$([A-Za-z_][A-Za-z0-9_]*)\]\}")
_BUILTINS = set(dir(builtins))
_LENIENT = {ast.FunctionDef: {"decorator_list", "returns", "type_params", "type_comment"},
            ast.AsyncFunctionDef: {"decorator_list", "returns", "type_params", "type_comment"},
            ast.arguments: {"posonlyargs", "vararg", "kwonlyargs", "kw_defaults", "kwarg", "defaults"}}
_SKIP = {"ctx", "type_comment", "kind"}
_BOUNDARY = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)


class RuleError(ValueError):
    """A rule the static semantics rejects."""


class _Abstain(Exception):
    """An instantiation the rule declines (a table without the key): no candidate."""


# ------------------------------------------------------------------ patterns
def _encode(text: str, sorts: dict[str, str]):
    """text with metavariables made Python: (code, operator metavariables as
    (byte offset, name)). Records each metavariable's sort in ``sorts``."""
    out, ops, pos = [], [], 0
    for m in _MV.finditer(text):
        out.append(text[pos:m.start()])
        star, name, sort = m.groups()
        if name == "_" and not star:
            out.append("__mvw")
        elif name == "_":                                      # $*_: an anonymous run
            k = sum(1 for x in sorts if x.startswith("_w"))
            sorts[f"_w{k}"] = "Expr"
            out.append(f"__mvs__w{k}")
        else:
            if sort is not None and sort not in SORTS:
                raise RuleError(f"unknown sort {sort!r} of ${name}")
            if sort and sorts.get(name, sort) != sort:
                raise RuleError(f"${name} has two sorts, {sorts[name]} and {sort}")
            sort = sorts.setdefault(name, sort or ("Stmts" if star and _own_line(text, m) else "Expr"))
            if sort in _OPS:
                ops.append((len("".join(out).encode()), name))
                out.append(_OPS[sort])
            else:
                out.append(("__mvs_" if star or sort == "Stmts" else "__mv_") + name)
        pos = m.end()
    out.append(text[pos:])
    return "".join(out), ops


def _own_line(text: str, m) -> bool:
    a = text.rfind("\n", 0, m.start()) + 1
    b = text.find("\n", m.end())
    return text[a:m.start()].strip() == "" and text[m.end():(b if b >= 0 else len(text))].strip() == ""


def _offsets(code: str):
    starts, acc = [0], 0
    for line in code.encode().split(b"\n"):
        acc += len(line) + 1
        starts.append(acc)
    return lambda ln, col: starts[ln - 1] + col


def _op_sites(tree: ast.AST, code: str, ops) -> dict:
    """{(id(node), index): name} for each operator metavariable."""
    off, sites = _offsets(code), {}
    beg = lambda n: off(n.lineno, n.col_offset)          # noqa: E731
    end = lambda n: off(n.end_lineno, n.end_col_offset)  # noqa: E731
    for at, name in ops:
        for n in ast.walk(tree):
            if isinstance(n, ast.Compare):
                parts = [n.left] + n.comparators
                hit = [i for i in range(len(n.ops)) if end(parts[i]) <= at < beg(parts[i + 1])]
            elif isinstance(n, ast.BinOp):
                hit = [0] if end(n.left) <= at < beg(n.right) else []
            elif isinstance(n, ast.AugAssign):
                hit = [0] if end(n.target) <= at < beg(n.value) else []
            elif isinstance(n, ast.BoolOp):
                hit = [0] if any(end(a) <= at < beg(b) for a, b in zip(n.values, n.values[1:])) else []
            else:
                hit = []
            if hit:
                sites[(id(n), hit[0])] = name
                break
        else:
            raise RuleError(f"operator ${name} is not between two operands")
    return sites


_HDR = "__hdr__"
_COMPOUND = (ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.FunctionDef, ast.AsyncFunctionDef)


def _header_body(code: str) -> str:
    """code whose last line is a compound statement's header (``while c:``),
    given a placeholder body: the rule then speaks of the header alone."""
    last = code.rstrip().split("\n")[-1]
    if not last.rstrip().endswith(":"):
        return code
    return code.rstrip() + "\n" + last[:len(last) - len(last.lstrip())] + "    " + _HDR


def _headers(tree: ast.AST) -> set:
    return {id(n) for n in ast.walk(tree) if isinstance(n, _COMPOUND) and len(n.body) == 1
            and isinstance(n.body[0], ast.Expr) and isinstance(n.body[0].value, ast.Name)
            and n.body[0].value.id == _HDR}


@dataclass
class Pattern:
    text: str
    nodes: list            # one expr, one stmt, or a run of stmts
    kind: str              # "expr" | "stmt" | "run"
    ops: dict              # {(id(pattern node), op index): name}
    names: set             # identifiers the pattern mentions literally
    headers: set = field(default_factory=set)   # header-only compound statements


def compile_pattern(text: str, sorts: dict[str, str], allow_run: bool = True) -> Pattern:
    code, ops = _encode(textwrap.dedent(text).strip("\n"), sorts)
    code = _header_body(code)
    try:
        tree, kind = ast.parse(code.strip(), mode="eval"), "expr"
        code = code.strip()
        nodes = [tree.body]
    except SyntaxError:
        try:
            tree = ast.parse(code)
        except SyntaxError as e:
            raise RuleError(f"pattern does not parse: {e.msg}: {text.strip()!r}") from None
        nodes = tree.body
        if not nodes:
            raise RuleError("empty pattern")
        kind = "stmt" if len(nodes) == 1 else "run"
        if kind == "run" and (not allow_run or len(nodes) > 3):
            raise RuleError("a pattern matches one expression, one statement, or two or three statements")
    if any(isinstance(n, _DEFS) for n in nodes) and allow_run:
        raise RuleError("a definition (def or class) is never a hole")
    names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)
             and not n.id.startswith("__mv") and n.id != _HDR}
    return Pattern(text, nodes, kind, _op_sites(tree, code, ops), names, _headers(tree))


def _mv(node, sorts):
    """(name, sort, is_sequence) if node is a metavariable placeholder."""
    s = node.id if isinstance(node, ast.Name) else node.arg if isinstance(node, ast.arg) else None
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Name):
        s = node.value.id
    if not s or not s.startswith("__mv") or s == "__mvw":
        return None
    seq = s.startswith("__mvs_")
    name = s[6:] if seq else s[5:]
    return name, sorts.get(name, "Expr"), seq


def _same(a, b) -> bool:
    if isinstance(a, list) or isinstance(b, list):
        return isinstance(a, list) and isinstance(b, list) and len(a) == len(b) and all(map(_same, a, b))
    if isinstance(a, ast.AST) and isinstance(b, ast.AST):
        return _dump(a) == _dump(b)
    if isinstance(a, type) or isinstance(b, type):
        return a is b
    return _ident(a) == _ident(b)


def _ident(v):
    return v.id if isinstance(v, ast.Name) else v.arg if isinstance(v, ast.arg) else v


def _bind(s: dict, name: str, v):
    if name in s:
        return s if _same(s[name], v) else None
    return {**s, name: v}


def _sort_ok(sort: str, n) -> bool:
    if sort == "Name":
        return isinstance(n, ast.Name)
    if sort == "Int":
        return isinstance(n, ast.Constant) and type(n.value) is int
    if sort == "Str":
        return isinstance(n, ast.Constant) and isinstance(n.value, str)
    if sort == "Const":
        return isinstance(n, ast.Constant)
    if sort in ("Stmt", "Stmts"):
        return isinstance(n, ast.stmt)
    return isinstance(n, ast.expr)


class _Matcher:
    def __init__(self, sorts: dict, ops: dict, headers: set = frozenset()):
        self.sorts, self.ops, self.headers = sorts, ops, headers

    def node(self, p, n, s):
        """Every extension of s under which pattern node p matches node n."""
        if isinstance(p, str):                           # a name of a global or nonlocal
            yield from self.value(None, None, p, n, s)
            return
        if isinstance(p, ast.Name) and p.id in ("__mvw", "_"):
            yield s
            return
        mv = _mv(p, self.sorts) if isinstance(p, ast.Name) else None
        if isinstance(p, ast.expr) and isinstance(n, ast.Expr) and not (mv and mv[1] in ("Stmt", "Stmts")):
            yield from self.node(p, n.value, s)              # an expression statement's expression
            return
        if mv:
            name, sort, seq = mv
            if not seq and _sort_ok(sort, n) and (t := _bind(s, name, n)) is not None:
                yield t
            return
        if isinstance(p, ast.Expr) and (mv := _mv(p, self.sorts)) and mv[1] in ("Stmt", "Stmts"):
            if isinstance(n, ast.stmt) and (t := _bind(s, mv[0], n)) is not None:
                yield t
            return
        if type(p) is not type(n):
            return
        if isinstance(p, ast.Constant):
            if type(p.value) is type(n.value) and p.value == n.value:
                yield s
            return
        yield from self.fields(p, n, s, list(p._fields))

    def fields(self, p, n, s, fs):
        if not fs:
            yield s
            return
        f, rest = fs[0], fs[1:]
        if f in _SKIP:
            yield from self.fields(p, n, s, rest)
            return
        if id(p) in self.headers and f in ("body", "orelse"):    # the header's own body, kept
            yield from self.fields(p, n, {**s, "__hdr_" + f: list(getattr(n, f, None) or [])}, rest)
            return
        a, b = getattr(p, f, None), getattr(n, f, None)
        if f in _LENIENT.get(type(p), ()) and a in (None, []):
            yield from self.fields(p, n, s, rest)
            return
        for t in self.value(p, f, a, b, s):
            yield from self.fields(p, n, t, rest)

    def value(self, p, f, a, b, s):
        if isinstance(a, list):
            if f == "ops":                                   # Compare's operators
                if not isinstance(b, list) or len(a) != len(b):
                    return
                t = s
                for i, (x, y) in enumerate(zip(a, b)):
                    t = self.op(p, i, x, y, t)
                    if t is None:
                        return
                yield t
                return
            if isinstance(b, list):
                yield from self.seq(a, b, s)
            return
        if isinstance(a, ast.AST):
            if isinstance(a, (ast.operator, ast.boolop, ast.unaryop, ast.cmpop)):
                if (t := self.op(p, 0, a, b, s)) is not None:
                    yield t
                return
            if isinstance(b, ast.AST):
                yield from self.node(a, b, s)
            return
        if isinstance(a, str) and a.startswith("__mv_") and isinstance(b, str):
            if (t := _bind(s, a[5:], b)) is not None:
                yield t
            return
        if a == "__mvw" or a == b:
            yield s

    def op(self, p, i, a, b, s):
        name = self.ops.get((id(p), i))
        if name is None:
            return s if type(a) is type(b) else None
        if not isinstance(b, _FAMILY[self.sorts[name]]):
            return None
        return _bind(s, name, type(b))

    def seq(self, ps, ns, s):
        if not ps:
            if not ns:
                yield s
            return
        mv = _mv(ps[0], self.sorts) if isinstance(ps[0], (ast.Name, ast.arg, ast.Expr)) else None
        if mv and (mv[2] or mv[1] == "Stmts"):
            for k in range(len(ns) + 1):
                if (t := _bind(s, mv[0], list(ns[:k]))) is not None:
                    yield from self.seq(ps[1:], ns[k:], t)
            return
        if not ns:
            return
        for t in self.node(ps[0], ns[0], s):
            yield from self.seq(ps[1:], ns[1:], t)


# ------------------------------------------------------------------ guards
_PRIMS = {"match": 2, "some": 2, "regex": 2, "builtin": 1, "load": 1, "bound": 1, "text": 1, "kind": 1, "len": 1,
          "field": 2, "parent": 1, "inside": 1, "first": 0, "last": 0, "prev": 1, "next": 1,
          "before": 1, "after": 1}
_PATTERN_ARG = {"match": 1, "some": 1, "parent": 0, "inside": 0, "prev": 0, "next": 0, "before": 0, "after": 0}
_NONREGULAR = re.compile(r"\\[1-9]|\(\?P=|\(\?[=!<]")


def _encode_guard(text: str) -> str:
    """$X -> __mv_X outside string literals."""
    out, i, q = [], 0, None
    while i < len(text):
        c = text[i]
        if q:
            out.append(c)
            if c == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 1
            elif text.startswith(q, i):
                out.append(text[i + 1:i + len(q)])
                i += len(q) - 1
                q = None
        elif c in "'\"":
            q = c * 3 if text.startswith(c * 3, i) else c
            out.append(q)
            i += len(q) - 1
        elif c == "$" and (m := _MV.match(text, i)):
            out.append("__mvw" if m.group(2) == "_" else "__mv_" + m.group(2))
            i = m.end() - 1
        else:
            out.append(c)
        i += 1
    return "".join(out)


class _Guard:
    """A compiled guard: the formula, and the patterns its primitives name."""

    def __init__(self, text: str, sorts: dict):
        try:
            self.tree = ast.parse("(\n" + _encode_guard(textwrap.dedent(text).strip()) + "\n)", mode="eval").body
        except SyntaxError as e:
            raise RuleError(f"guard does not parse: {e.msg}") from None
        self.sorts, self.patterns, self.names = sorts, {}, set()
        self.tree = _Sugar().visit(self.tree)
        self._check(self.tree)

    def _check(self, g):
        if isinstance(g, ast.BoolOp) or (isinstance(g, ast.UnaryOp) and isinstance(g.op, ast.Not)):
            for v in (g.values if isinstance(g, ast.BoolOp) else [g.operand]):
                self._check(v)
        elif isinstance(g, ast.Compare):
            for v in [g.left] + g.comparators:
                self._term(v)
        elif isinstance(g, ast.Call):
            self._call(g)
        elif not (isinstance(g, ast.Constant) and isinstance(g.value, bool)):
            raise RuleError(f"guard: unsupported form {ast.unparse(g)!r}")

    def _term(self, v):
        if isinstance(v, ast.Name) and v.id.startswith("__mv_"):
            return
        if isinstance(v, ast.Constant) or (isinstance(v, (ast.Set, ast.List, ast.Tuple))
                                           and all(isinstance(e, ast.Constant) for e in v.elts)):
            return
        if isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id in ("text", "kind", "len"):
            self._call(v)
            return
        raise RuleError(f"guard: unsupported term {ast.unparse(v)!r}")

    def _call(self, c):
        f = c.func.id if isinstance(c.func, ast.Name) else None
        if f not in _PRIMS or len(c.args) != _PRIMS[f] or c.keywords:
            raise RuleError(f"guard: unknown primitive or wrong arity: {ast.unparse(c)!r}")
        for i, a in enumerate(c.args):
            if _PATTERN_ARG.get(f) == i:
                if not (isinstance(a, ast.Constant) and isinstance(a.value, str)):
                    raise RuleError(f"{f}: the pattern must be a string literal")
                pat = compile_pattern(a.value, self.sorts, allow_run=False)
                self.patterns[id(a)] = pat
                self.names |= pat.names
            elif f == "regex" and i == 1:
                if not (isinstance(a, ast.Constant) and isinstance(a.value, str)) or _NONREGULAR.search(a.value):
                    raise RuleError("regex: a string literal without back-references or look-around")
                re.compile(a.value)
            elif f == "field":
                if not (isinstance(a, ast.Constant) and isinstance(a.value, str)):
                    raise RuleError("field: two string literals")
            elif not (isinstance(a, ast.Name) and a.id.startswith("__mv")):
                raise RuleError(f"{f}: argument must be a metavariable")

    def eval(self, g, s, hole):
        """Every extension of s that satisfies g (a finite, ordered list)."""
        if isinstance(g, ast.BoolOp):
            if isinstance(g.op, ast.And):
                cur = [s]
                for v in g.values:
                    cur = [t for c in cur for t in self.eval(v, c, hole)]
                return cur
            return [t for v in g.values for t in self.eval(v, s, hole)]
        if isinstance(g, ast.UnaryOp):
            return [] if self.eval(g.operand, s, hole) else [s]
        if isinstance(g, ast.Constant):
            return [s] if g.value else []
        if isinstance(g, ast.Compare):
            terms = [self._value(v, s, hole) for v in [g.left] + g.comparators]
            if any(t is _UNBOUND for t in terms):
                return []
            return [s] if all(_cmp(op, *_as_text(x, y, hole.ctx))
                              for op, x, y in zip(g.ops, terms, terms[1:])) else []
        return self._prim(g, s, hole)

    def _value(self, v, s, hole):
        if isinstance(v, ast.Name):
            return s.get(v.id[5:], _UNBOUND)
        if isinstance(v, ast.Constant):
            return v.value
        if isinstance(v, (ast.Set, ast.List, ast.Tuple)):
            return frozenset(e.value for e in v.elts)
        x = s.get(v.args[0].id[5:], _UNBOUND)
        if x is _UNBOUND:
            return x
        if v.func.id == "text":
            return _text(x, hole.ctx)
        if v.func.id == "len":
            return len(x) if isinstance(x, list) else 1
        return type(x).__name__ if isinstance(x, ast.AST) else "Ident" if isinstance(x, str) else "Op"

    def _prim(self, c, s, hole):
        f, a = c.func.id, c.args
        gp = self.patterns[id(a[_PATTERN_ARG[f]])] if f in _PATTERN_ARG else None
        m = _Matcher(self.sorts, gp.ops, gp.headers) if gp else None
        pat = lambda: self.patterns[id(a[_PATTERN_ARG[f]])].nodes[0]       # noqa: E731
        arg = lambda i: s.get(a[i].id[5:], _UNBOUND)                         # noqa: E731
        if f == "bound":
            return [] if arg(0) is _UNBOUND else [s]
        if f in ("match", "some", "regex", "builtin", "load") and arg(0) is _UNBOUND:
            return []
        if f == "match":
            return list(m.node(pat(), arg(0), s)) if isinstance(arg(0), ast.AST) else []
        if f == "some":
            roots = arg(0) if isinstance(arg(0), list) else [arg(0)]
            return [t for r in roots if isinstance(r, ast.AST) for d in ast.walk(r) for t in m.node(pat(), d, s)]
        if f == "regex":
            return [s] if re.fullmatch(a[1].value, _text(arg(0), hole.ctx)) else []
        if f == "builtin":
            return [s] if _ident(arg(0)) in _BUILTINS else []
        if f == "load":
            return [s] if isinstance(arg(0), ast.Name) and isinstance(arg(0).ctx, ast.Load) else []
        if f == "field":
            at = hole.nodes[0] if a[0].value == "Expr" else hole.anchor
            par = hole.ctx.parent(at)
            return [s] if (type(par).__name__ == a[0].value and hole.ctx.field(at) == a[1].value) else []
        if f == "parent":
            par = hole.ctx.parent(hole.anchor)
            return list(m.node(pat(), par, s)) if par is not None else []
        if f == "inside":
            p, n = pat(), hole.ctx.parent(hole.anchor)
            while n is not None and not isinstance(n, ast.Module):
                if type(n) is type(p):
                    return list(m.node(p, n, s))
                if isinstance(n, _BOUNDARY):
                    return []
                n = hole.ctx.parent(n)
            return []
        sib, i, j = hole.siblings()
        if sib is None:
            return []
        if f == "first":
            return [s] if i == 0 else []
        if f == "last":
            return [s] if j == len(sib) else []
        span = {"prev": sib[i - 1:i] if i > 0 else [], "next": sib[j:j + 1],
                "before": sib[:i], "after": sib[j:]}[f]
        return [t for n in span for t in m.node(pat(), n, s)]


_UNBOUND = object()


class _Sugar(ast.NodeTransformer):
    """``G == False`` is ``not G`` and ``G == True`` is ``G``, for a formula G."""

    def visit_Compare(self, c):
        self.generic_visit(c)
        g, k = c.left, c.comparators[0]
        if (len(c.ops) == 1 and isinstance(k, ast.Constant) and isinstance(k.value, bool)
                and isinstance(c.ops[0], (ast.Eq, ast.NotEq, ast.Is, ast.IsNot))
                and (isinstance(g, (ast.BoolOp, ast.UnaryOp)) or
                     (isinstance(g, ast.Call) and getattr(g.func, "id", None) not in ("text", "kind", "len")))):
            keep = k.value != isinstance(c.ops[0], (ast.NotEq, ast.IsNot))
            return g if keep else ast.UnaryOp(op=ast.Not(), operand=g)
        return c


def _cmp(op, x, y) -> bool:
    if isinstance(op, (ast.In, ast.NotIn)):
        hit = (x if isinstance(x, (str, int, float)) else _scalar(x)) in y if isinstance(y, frozenset) else False
        return hit if isinstance(op, ast.In) else not hit
    if isinstance(op, (ast.Eq, ast.NotEq)):
        eq = _same(x, y) if not (isinstance(x, (str, int, float)) or isinstance(y, (str, int, float))) \
            else _scalar(x) == _scalar(y)
        return eq if isinstance(op, ast.Eq) else not eq
    x, y = _scalar(x), _scalar(y)
    if not (isinstance(x, (int, float)) and isinstance(y, (int, float))):
        return False
    return {ast.Lt: x < y, ast.LtE: x <= y, ast.Gt: x > y, ast.GtE: x >= y}[type(op)]


def _scalar(v):
    if isinstance(v, ast.Constant):
        return v.value
    if isinstance(v, type):
        return _TOK[v]
    return _ident(v)


def _as_text(x, y, ctx):
    """A binding compared with a string or a set of strings is compared by its text."""
    def lit(v):
        return isinstance(v, str) or (isinstance(v, frozenset) and all(isinstance(e, str) for e in v))
    def conv(v):
        return _text(v, ctx) if isinstance(v, (ast.AST, type, list)) and not isinstance(v, ast.Constant) else v
    return (conv(x), y) if lit(y) else (x, conv(y)) if lit(x) else (x, y)


def _text(v, ctx: Ctx) -> str:
    if isinstance(v, type):
        return _TOK[v]
    if isinstance(v, str):
        return v
    if isinstance(v, list):
        return ", ".join(_text(x, ctx) for x in v)
    if isinstance(v, ast.Module):
        return ctx.source
    if hasattr(v, "lineno"):
        return ctx.text(v)
    return ast.unparse(v)


@dataclass
class _Hole:
    nodes: list
    ctx: Ctx

    @property
    def anchor(self):
        """Where the hole sits: an expression statement's expression sits where its statement does."""
        n = self.nodes[0]
        par = self.ctx.parent(n)
        return par if isinstance(n, ast.expr) and isinstance(par, ast.Expr) else n

    def siblings(self):
        """(statement list the hole sits in, its first index, one past its last)."""
        a = self.anchor
        if a is not self.nodes[0]:
            par, f = self.ctx.parent(a), self.ctx.field(a)
            sib = getattr(par, f, None) if par is not None else None
            if not isinstance(sib, list):
                return None, 0, 0
            i = next(k for k, x in enumerate(sib) if x is a)
            return sib, i, i + 1
        par, f = self.ctx.parent(self.nodes[0]), self.ctx.field(self.nodes[0])
        sib = getattr(par, f, None) if par is not None else None
        if not isinstance(sib, list) or not isinstance(self.nodes[0], ast.stmt):
            return None, 0, 0
        i = next(k for k, x in enumerate(sib) if x is self.nodes[0])
        return sib, i, i + len(self.nodes)


# ------------------------------------------------------------------ templates
@dataclass
class Template:
    text: str
    tree: ast.AST          # Expression or Module, with placeholders
    ops: dict
    tables: dict           # {placeholder: (table, metavariable)}
    binders: set           # names the template binds at statement level
    headers: set = field(default_factory=set)


def _binders(tree: ast.AST) -> tuple[set, set]:
    """(names bound at the template's top level, names bound in a nested scope)."""
    top, nested = set(), set()

    def visit(n, inner):
        if isinstance(n, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            inner = True
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            (nested if inner else top).add(n.id)
        elif isinstance(n, ast.arg):
            nested.add(n.arg)
        elif isinstance(n, ast.ExceptHandler) and n.name:
            top.add(n.name)
        for c in ast.iter_child_nodes(n):
            visit(c, inner)
    visit(tree, False)
    return {b for b in top if not b.startswith("__mv")}, {b for b in nested if not b.startswith("__mv")}


def compile_template(text: str, hole: str, sorts: dict, tables: dict) -> Template:
    lookups = {}

    def table(m):
        t, k = m.groups()
        if t not in tables:
            raise RuleError(f"template uses table {t!r}, which the rule does not define")
        vals = list(tables[t].values())
        ph = f"__tb{len(lookups)}"
        lookups[ph] = (t, k)
        if vals and all(v in _TOK.values() for v in vals):          # an operator table
            sort = next(s for s, fam in _FAMILY.items()
                        if all(any(issubclass(c, fam) and _TOK[c] == v for c in _TOK) for v in vals))
            sorts.setdefault(ph, sort)
            return f"${ph}"
        return ph

    body = textwrap.dedent(text).strip("\n")
    code, ops = _encode(_TB.sub(table, body), sorts)
    if hole != "expr":
        code = _header_body(code)
    try:
        tree = ast.parse(code.strip(), mode="eval") if hole == "expr" else ast.parse(code)
    except SyntaxError as e:
        raise RuleError(f"template does not parse as {'an expression' if hole == 'expr' else 'statements'}: "
                        f"{e.msg}: {text.strip()!r}") from None
    if hole == "expr":
        code = code.strip()
    top, nested = _binders(tree)
    return Template(text, tree, _op_sites(tree, code, ops), lookups, top | nested, _headers(tree))


# ------------------------------------------------------------------ rules
@dataclass
class LangRule:
    name: str
    symptoms: tuple
    patterns: list
    guard: _Guard | None
    templates: list
    tables: dict
    sorts: dict
    hole: str
    k: int = 1             # statements in a run hole
    literal: set = field(default_factory=set)   # names the patterns mention literally

    def apply(self, source: str) -> list[str]:
        tree = ast.parse(source)
        ctx = Ctx(source, tree)
        names = {getattr(n, "id", None) or getattr(n, "arg", None) or getattr(n, "name", None)
                 for n in ast.walk(tree) if isinstance(n, (ast.Name, ast.arg) + _DEFS)}
        out, outside = [], {}
        for hole in self._holes(tree, ctx):
            for pat in self.patterns:
                m = _Matcher(self.sorts, pat.ops, pat.headers)
                for s in m.seq(pat.nodes, hole.nodes, {"MODULE": tree}):
                    for t in (self.guard.eval(self.guard.tree, s, hole) if self.guard else [s]):
                        for tpl in self.templates:
                            carries = any(_binds(t[x]) for x in _carried(self, pat, tpl) if x in t)
                            try:
                                text = _instantiate(tpl, t, ctx, names, self.sorts, self.tables, self.literal)
                            except _Abstain:
                                continue
                            if _unchanged(text, hole.nodes, self.hole):
                                continue
                            cand = (substitute(source, tree, ctx, hole.nodes[0], text, outside)
                                    if self.hole != "run" else _substitute_run(source, tree, ctx, hole.nodes, text))
                            if carries and cand is not None and not _keeps_scope(
                                    ctx, hole.nodes, cand, self._names(t)):
                                continue
                            if cand is not None and cand != source and cand not in out:
                                out.append(cand)
        return out

    def _names(self, t: dict):
        """σ(N): the names the effect lists under this binding, every name a table may supply included."""
        out = set()
        for x in effect(self)[0]:
            if x == "*":
                out.update(v for tb in self.tables.values() for v in tb.values())
            else:
                out.add(_ident(t.get(x[1:])) if x.startswith("$") else x)
        return out

    def _holes(self, tree, ctx):
        if self.hole != "run":
            for n in ast.walk(tree):                       # breadth-first: a fixed order
                if (isinstance(n, ast.expr) if self.hole == "expr"
                        else isinstance(n, ast.stmt) and not isinstance(n, _DEFS)):
                    yield _Hole([n], ctx)
            return
        for n in ast.walk(tree):
            for f in ("body", "orelse", "finalbody"):
                block = getattr(n, f, None)
                if isinstance(block, list) and block and isinstance(block[0], ast.stmt):
                    for i in range(len(block) - self.k + 1):
                        run = block[i:i + self.k]
                        if not any(isinstance(x, _DEFS) for x in run):
                            yield _Hole(run, ctx)

    def rule(self) -> Rule:
        return Rule(name=self.name, apply=self.apply, symptoms=self.symptoms, local=True, total=True,
                    neutral=scope_neutral(self))


def _placeholders(nodes) -> dict:
    """{metavariable: the scopes it occurs at}, 0 for the fragment's own scope, 1 inside a
    comprehension only (a walrus there still binds in the own scope), 2 inside a nested
    function, lambda, or class."""
    out = {}

    def walk(n, inner):
        for _, v in ast.iter_fields(n):
            for y in (v if isinstance(v, list) else [v]):
                if isinstance(y, str) and y.startswith("__mv") and y != "__mvw":
                    out.setdefault(y[6:] if y.startswith("__mvs_") else y[5:], set()).add(inner)
        inner = 2 if isinstance(n, _SCOPE) else max(inner, 1) if isinstance(n, _COMP) else inner
        for c in ast.iter_child_nodes(n):
            walk(c, inner)
    for n in nodes:
        walk(n, 0)
    return out


_CARRIED: dict = {}


def _carried(rule, pat, tpl) -> frozenset:
    """The metavariables that the template omits, brings in from a guard, or moves into or
    out of a nested scope, unless the rule's effect already lists them or lets the kind change:
    the code they match leaves the hole's scope, so where that code binds, declares, or
    yields, the engine applies the template only if the scope's bindings, declarations,
    and kind stay as they were, but for the names the effect lists (Definition 3.4),
    which keeps the scope effect sound."""
    key = (id(rule), id(pat), id(tpl))
    if key not in _CARRIED:
        n, kind = effect(rule)
        p = _placeholders(pat.nodes)
        t = _placeholders(tpl.tree.body if isinstance(tpl.tree, ast.Module) else [tpl.tree.body])
        _CARRIED[key] = (rule, pat, tpl, frozenset() if kind else frozenset(
            x for x in p.keys() | t.keys() if p.get(x) != t.get(x) and "$" + x not in n))
    return _CARRIED[key][3]


def _binds(v) -> bool:
    nodes = v if isinstance(v, list) else [v]
    nodes = [n for n in nodes if isinstance(n, ast.AST)]
    names, declared, kind = _own_effects(nodes)
    return bool(names or declared or kind)


def _keeps_scope(ctx: Ctx, hole: list, cand: str, allowed) -> bool:
    """Whether ``cand`` keeps the kind of the hole's scope and of every function both programs
    have, and every name it binds or declares differently from the program, but for ``allowed``
    and names the program lacks, occurs nowhere in that scope or the scopes nested in it
    outside the hole."""
    node = hole[0]
    steps, up = _path(ctx, node), node
    while not isinstance(up, _SCOPE + (ast.Module,)):
        up = ctx._parent[id(up)][0]
    steps = steps[:len(_path(ctx, up))]
    try:
        other = ast.parse(cand)
    except SyntaxError:
        return False
    for f, i in steps:
        other = getattr(other, f) if i is None else getattr(other, f)[i]
    body = lambda n: n.body if isinstance(n.body, list) else [n.body]
    (pn, pd, pk), (qn, qd, qk) = _own_effects(body(up)), _own_effects(body(other))
    every = lambda t: {getattr(n, "id", None) or getattr(n, "arg", None) or getattr(n, "name", None)
                       or getattr(n, "asname", None) for n in ast.walk(t)}
    fresh = every(ast.parse(cand)) - every(ctx.tree)
    a, b = _kinds(ctx.tree), _kinds(ast.parse(cand))
    if pk != qk or any(a[k] != b[k] for k in a.keys() & b.keys()):
        return False
    changed = ((pn ^ qn) | {x for _, x in pd ^ qd}) - allowed - fresh
    if not changed:
        return True
    inside = {id(n) for h in hole for n in ast.walk(h)}
    return not any(id(n) not in inside and x in changed for n in ast.walk(up)
                   for x in (getattr(n, "id", None), getattr(n, "arg", None),
                             getattr(n, "name", None), *getattr(n, "names", ())))


def _instantiate(tpl: Template, s: dict, ctx: Ctx, names: set, sorts: dict, tables: dict,
                 literal: set) -> str:
    """inst(T, σ): the template's tree with every placeholder replaced by its
    binding, statement-level binders renamed apart from the program's names.
    Bindings are spliced by reference: they are never visited or mutated, and
    keep their locations, so only the template's own nodes are copied."""
    rename = {}
    for b in sorted(tpl.binders - literal):
        if b in names:
            k = 1
            while f"{b}_{k}" in names:
                k += 1
            rename[b] = f"{b}_{k}"
    tree = copy.deepcopy(tpl.tree)
    twin = {id(o): n for o, n in zip(ast.walk(tpl.tree), ast.walk(tree))}   # same traversal order
    new_ops = {(id(twin[nid]), i): name for (nid, i), name in tpl.ops.items()}
    hdrs = {id(twin[h]) for h in tpl.headers}

    def lookup(ph):
        t, k = tpl.tables[ph]
        key = _text(s[k], ctx) if k in s else None
        if key not in tables[t]:
            raise _Abstain
        return tables[t][key]

    def value(name):
        if name.startswith("__tb"):
            return lookup(name)
        if name not in s:
            raise _Abstain
        return s[name]

    def as_expr(v):
        if isinstance(v, ast.expr):
            return v
        if isinstance(v, str):
            try:
                return ast.parse(v, mode="eval").body
            except SyntaxError:
                raise _Abstain from None
        raise _Abstain

    def ident(v):
        v = _ident(v)
        if isinstance(v, str) and v.isidentifier():
            return v
        raise _Abstain

    class Fill(ast.NodeTransformer):
        def generic_visit(self, node):
            for f, val in ast.iter_fields(node):
                if isinstance(val, list):
                    out = []
                    for x in val:
                        mv = _mv(x, sorts) if isinstance(x, (ast.Name, ast.arg, ast.Expr)) else None
                        if mv and (mv[2] or mv[1] in ("Stmts", "Stmt")):
                            v = value(mv[0])
                            out.extend(v if isinstance(v, list) else [v])
                            continue
                        if isinstance(x, ast.AST):
                            y = self.visit(x)
                            if y is None:
                                continue
                            out.extend(y if isinstance(y, list) else [y])
                        else:
                            out.append(x)
                    setattr(node, f, out)
                elif isinstance(val, ast.AST):
                    setattr(node, f, self.visit(val))
                elif isinstance(val, str) and (val.startswith("__mv_") or val.startswith("__tb")):
                    setattr(node, f, ident(value(val[5:] if val.startswith("__mv_") else val)))
                elif isinstance(val, str) and f in ("id", "arg") and val in rename:
                    setattr(node, f, rename[val])
            if id(node) in hdrs:                            # a header keeps the matched body
                if "__hdr_body" not in s:
                    raise _Abstain
                node.body = s["__hdr_body"] or [ast.Pass()]
                if hasattr(node, "orelse"):
                    node.orelse = s.get("__hdr_orelse", [])
            for i, name in [(i, nm) for (nid, i), nm in new_ops.items() if nid == id(node)]:
                op = value(name)
                op = op if isinstance(op, type) else next((c for c, t in _TOK.items() if t == op), None)
                if op is None:
                    raise _Abstain
                if isinstance(node, ast.Compare):
                    node.ops[i] = op()
                else:
                    node.op = op()
            return node

        def visit_Name(self, node):
            if node.id.startswith("__mv_") or node.id.startswith("__tb"):
                return as_expr(value(node.id[5:] if node.id.startswith("__mv_") else node.id))
            if node.id in rename:
                node.id = rename[node.id]
            return node

        def visit_Expr(self, node):
            if isinstance(node.value, ast.Name) and node.value.id.startswith("__mv_"):
                v = value(node.value.id[5:])
                if isinstance(v, ast.stmt):
                    return v
            return self.generic_visit(node)

    tree = Fill().visit(tree)
    # Name closure: a name the program lacks, written in a negated guard, an
    # alternative that did not match, or a table, yields no candidate.
    fresh = {rename.get(b, b) for b in tpl.binders - literal}
    if any(isinstance(n, ast.Name) and n.id not in names and n.id not in _BUILTINS and n.id not in fresh
           for n in ast.walk(tree)):
        raise _Abstain
    ast.fix_missing_locations(tree)
    return ast.unparse(tree.body if isinstance(tree, ast.Expression) else tree)


def _unchanged(text: str, nodes: list, hole: str) -> bool:
    """The instantiated template is the hole's own code (it may differ only in spelling)."""
    try:
        new = [ast.parse(text, mode="eval").body] if hole == "expr" else ast.parse(text).body
    except SyntaxError:
        return False
    return _dump(new) == _dump(nodes)


def _substitute_run(source: str, tree: ast.AST, ctx: Ctx, nodes: list, text: str) -> str | None:
    """source with the run of statements ``nodes`` replaced by text (Section 3.2)."""
    path = _path(ctx, nodes[0])
    held = _holed(tree, path, len(nodes))
    if not path or path[-1][1] is None or held is None:
        return None
    outside = held[0]
    try:
        new = ast.parse(text).body
    except SyntaxError:
        return None
    s, e = ctx.span(nodes[0])[0], ctx.span(nodes[-1])[1]
    line_start = source.rfind("\n", 0, s) + 1
    indent = source[line_start:s]
    if not new:
        siblings = getattr(ctx.parent(nodes[0]), path[-1][0])
        if len(siblings) == len(nodes):
            cand, new = source[:s] + "pass" + source[e:], [ast.Pass()]
        else:
            line_end = source.find("\n", e)
            cand = source[:line_start] + (source[line_end + 1:] if line_end >= 0 else "")
    else:
        cand = source[:s] + ("\n" + indent).join(text.strip("\n").splitlines()) + source[e:]
    try:
        got = _holed(ast.parse(cand), path, len(new))
    except SyntaxError:
        return None
    return cand if got is not None and got[0] == outside and _dump(got[1]) == _dump(new) else None


# ------------------------------------------------------------------ the rule file
_KEYS = ("rule ", "symptoms:", "match:", "where:", "rewrite:", "table ")


def _sections(block: str) -> dict:
    out, key = {}, None
    for line in block.splitlines():
        if line.startswith("#"):
            continue
        k = next((k for k in _KEYS if line.startswith(k)), None)
        if k:
            key = k.strip(" :")
            rest = line[len(k):]
            if key == "table":
                out.setdefault("table", []).append(rest)
                key = "table_cont"
            else:
                out[key] = [rest] if rest.strip() else []
        elif key == "table_cont":
            out["table"][-1] += "\n" + line
        elif key is not None:
            out[key].append(line)
    return out


def _alternatives(lines: list[str]) -> list[str]:
    alts, cur = [], []
    for line in lines + ["|"]:
        if line.strip() == "|":
            if "\n".join(cur).strip():
                alts.append(textwrap.dedent("\n".join(cur)).strip("\n"))
            cur = []
        else:
            cur.append(line)
    return alts


def compile_rule(block: str) -> LangRule:
    sec = _sections(block)
    name = (sec.get("rule") or [""])[0].strip()
    if not name.isidentifier():
        raise RuleError(f"rule name {name!r} is not an identifier")
    tables = {}
    for t in sec.get("table", []):
        tname, _, lit = t.partition(":")
        try:
            val = ast.literal_eval(lit.strip())
        except (ValueError, SyntaxError):
            raise RuleError(f"table {tname.strip()}: not a dict literal") from None
        if not (isinstance(val, dict) and all(isinstance(k, str) and isinstance(v, str) for k, v in val.items())):
            raise RuleError(f"table {tname.strip()}: keys and values must be strings")
        tables[tname.strip()] = val
    sorts: dict[str, str] = {"MODULE": "Expr"}
    patterns = [compile_pattern(p, sorts) for p in _alternatives(sec.get("match", []))]
    if not patterns:
        raise RuleError(f"{name}: no match")
    kinds = {(p.kind, len(p.nodes)) for p in patterns}
    if len(kinds) != 1:
        raise RuleError(f"{name}: alternatives match holes of different kinds")
    hole, k = next(iter(kinds))
    guard_text = "\n".join(sec.get("where", [])).strip()
    guard = _Guard(guard_text, sorts) if guard_text else None
    bound = set(sorts) - {"MODULE"}
    texts = _alternatives(sec.get("rewrite", []))
    if "rewrite" in sec and not texts:
        texts = [""]                                           # an empty rewrite deletes the hole
    if not texts:
        raise RuleError(f"{name}: no rewrite")
    try:
        templates = [compile_template(t, "expr" if hole == "expr" else "stmts", sorts, tables) for t in texts]
    except RuleError:
        if hole != "expr":
            raise
        templates = [compile_template(t, "stmts", sorts, tables) for t in texts]   # re-raises if neither
        patterns = [Pattern(p.text, [ast.Expr(value=p.nodes[0])], "stmt", p.ops, p.names, p.headers)
                    for p in patterns]
        hole = "stmt"
    rule = LangRule(name, tuple(s.strip() for s in ",".join(sec.get("symptoms", [])).split(",") if s.strip()),
                    patterns, guard, templates, tables, sorts, hole, k,
                    set().union(*(p.names for p in patterns)) | (guard.names if guard else set()))
    _static(rule, bound)
    return rule


def _static(r: LangRule, bound: set) -> None:
    """The static semantics' rejections (Section 3.2)."""
    literal = r.literal
    for t in r.templates:
        used = {mv[0] for n in ast.walk(t.tree) if isinstance(n, (ast.Name, ast.arg))
                and (mv := _mv(n, r.sorts))}
        if used - bound:
            raise RuleError(f"{r.name}: template uses unbound ${sorted(used - bound)[0]}")
        free = {n.id for n in ast.walk(t.tree) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)
                and not n.id.startswith("__mv") and not n.id.startswith("__tb") and n.id != _HDR}
        bad = free - _BUILTINS - literal - t.binders
        if bad:
            raise RuleError(f"{r.name}: template names {sorted(bad)} come from neither the match nor builtins; "
                            "bind them with a metavariable (e.g. inside(\"def $f($p): $B:Stmts\"))")
        for p in r.patterns:
            pt = (ast.Expression(body=p.nodes[0]) if r.hole == "expr" else ast.Module(body=p.nodes, type_ignores=[]))
            if _dump(pt) == _dump(t.tree) and not p.ops and not t.ops and bool(p.headers) == bool(t.headers):
                raise RuleError(f"{r.name}: a rewrite equal to its match changes nothing")
        if r.hole == "stmt" and isinstance(r.patterns[0].nodes[0], ast.Return):
            body = t.tree.body if isinstance(t.tree, ast.Module) else []
            if body and not any(isinstance(x, ast.Return) for x in body):
                raise RuleError(f"{r.name}: a rewrite of a return must keep a return")


def compile_rules(text: str) -> tuple[list[LangRule], list[str]]:
    """Every rule of a rule file that the static semantics accepts, and the
    reasons it rejects the others."""
    blocks = re.split(r"(?m)^(?=rule )", text)
    rules, errors, seen = [], [], set()
    for b in blocks:
        if not b.strip().startswith("rule "):
            if b.strip() and not all(x.strip().startswith("#") or not x.strip() for x in b.splitlines()):
                errors.append(f"text outside a rule: {b.strip()[:60]!r}")
            continue
        try:
            r = compile_rule(b)
        except RuleError as e:
            errors.append(str(e))
            continue
        except RecursionError:
            errors.append("rule too deeply nested")
            continue
        if r.name in seen:
            errors.append(f"{r.name}: defined twice")
            continue
        seen.add(r.name)
        rules.append(r)
    return rules, errors


def load_rules(text: str) -> list[Rule]:
    return [r.rule() for r in compile_rules(text)[0]]



# ------------------------------------------------------------------ scope neutrality
_SCOPE = (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_COMP = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)


def _own_effects(nodes) -> tuple[set, set, bool]:
    """(the names a fragment binds in the scope it sits in, its global and nonlocal
    declarations as (kind, name), whether it yields or awaits). A comprehension's own variables
    stay in its scope, but a walrus inside it binds in the enclosing one."""
    names, declared, kind = set(), set(), False

    def walk(n, in_comp):
        nonlocal kind
        if isinstance(n, _SCOPE):
            if not isinstance(n, ast.Lambda) and not in_comp:
                names.add(n.name)
            return
        if isinstance(n, _COMP):
            for c in ast.iter_child_nodes(n):
                walk(c, True)
            return
        if isinstance(n, ast.NamedExpr):
            names.add(n.target.id)
        elif not in_comp and isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            names.add(n.id)
        elif not in_comp and isinstance(n, ast.ExceptHandler) and n.name:
            names.add(n.name)
        elif not in_comp and isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name:
            names.add(n.name)
        elif not in_comp and isinstance(n, (ast.Import, ast.ImportFrom)):
            names.update((a.asname or a.name).split(".")[0] for a in n.names)
        elif isinstance(n, (ast.Global, ast.Nonlocal)):
            declared.update((type(n), x) for x in n.names)
        if isinstance(n, (ast.Yield, ast.YieldFrom, ast.Await)):
            kind = True
        for c in ast.iter_child_nodes(n):
            walk(c, in_comp)
    for n in nodes:
        walk(n, False)
    return names, declared, kind


def effect(rule: LangRule) -> tuple[frozenset, bool]:
    """The rule's scope effect: (the metavariables, as ``$X``, and literal names whose
    binding or declaration in the hole's scope a rewrite may change; whether it may
    change the kind of the hole's scope or of a function the rule writes). A template's other binders are renamed apart from the
    program's names, so they bind nothing the program has. Every repair the rule makes
    has a footprint within its hole and the occurrences of these names in the hole's
    scope and the scopes nested in it, unless the kind may change (the paper's effect
    theorem); ``*`` stands for a name a table lookup supplies."""
    mv = lambda xs: {"$" + x[5:] if x.startswith("__mv_") else x for x in xs}
    out, kind = set(), False
    for p in rule.patterns:
        pn, pd, pk = _own_effects(p.nodes)
        for t in rule.templates:
            body = t.tree.body if isinstance(t.tree, ast.Module) else [t.tree.body]
            tn, td, tk = _own_effects(body)
            tn = {x for x in tn if x.startswith("__") or x in rule.literal}   # the rest are fresh
            out |= mv(pn ^ tn) | mv(x for _, x in pd ^ td)
            a, b = (_kinds(ast.Module(body=x, type_ignores=[])) for x in (p.nodes, body))
            kind |= pk != tk or any(a[k] != b[k] for k in a.keys() & b.keys())
    return frozenset("*" if x.startswith("__tb") else x for x in out), kind


def scope_neutral(rule: LangRule) -> bool:
    """A rule with no scope effect: every application leaves every name's
    classification and every function's kind unchanged, so its footprint is its hole
    (the paper's Corollary on scope-neutral rules)."""
    return effect(rule) == (frozenset(), False)


if __name__ == "__main__":                     # the language's own check
    src = ("def f(s, seq):\n    if s[1:].isupper():\n        return s.swapcase()\n"
           "    for i in range(len(seq)):\n        if seq[i] < 0:\n            return i\n    return len(seq)\n")
    rules, errs = compile_rules('''
rule rest_isupper_to_equality_form
symptoms: wrong
match: $X.isupper()
where: match($X, "$W[1:]")
rewrite: $X.upper() == $X

rule flip_compare
match: $a $o:Cmp $b
where: text($o) in {"<", "<="}
rewrite: $a ${flip[$o]} $b
table flip: {"<": "<=", "<=": "<"}

rule guard_empty
match: return $e
where: inside("def $f($*xs, $p, $*ys): $B:Stmts") and some($e, "len($q:Name)") and $q == $p
rewrite:
    if not $p:
        return 0
    return $e

rule bad_name
match: $v:Name
rewrite: helper($v)

rule identity
match: $X.isupper()
rewrite: $X.isupper()

rule swap_two
match:
    $a = $x
    $b = $y
where: $a == $y
rewrite:
    $b = $y
    $a = $x
''')
    assert [r.name for r in rules] == ["rest_isupper_to_equality_form", "flip_compare", "guard_empty", "swap_two"], \
        [r.name for r in rules]
    assert len(errs) == 2 and "helper" in errs[0] and "changes nothing" in errs[1], errs
    by = {r.name: r for r in rules}
    assert by["rest_isupper_to_equality_form"].apply(src) == \
        [src.replace("s[1:].isupper()", "s[1:].upper() == s[1:]")]
    assert by["flip_compare"].apply(src) == [src.replace("seq[i] < 0", "seq[i] <= 0")]
    g = by["guard_empty"].apply(src)
    assert len(g) == 1 and "    if not seq:\n        return 0\n    return len(seq)" in g[0], g
    sw = by["swap_two"].apply("x = 1\ny = x\nprint(y)\n")
    assert sw == ["y = x\nx = 1\nprint(y)\n"], sw
    more, errs2 = compile_rules('''
rule header_lt
match: while $c <= $k:
rewrite: while $c < $k:

rule split_append
match: $out.append($a.remove($m))
rewrite:
    $out.append($m)
    $a.remove($m)

rule no_len_guard
match: return $e
where: some($e, "len($_)") == False
rewrite: return $e + 1
''')
    assert not errs2, errs2
    hb = {r.name: r for r in more}
    loop = "out = []\nwhile len(out) <= 3:\n    out.append(xs.remove(max(xs)))\n"
    assert hb["header_lt"].apply(loop) == [loop.replace("<= 3", "< 3")]
    assert hb["split_append"].apply(loop) == [loop.replace(
        "    out.append(xs.remove(max(xs)))", "    out.append(max(xs))\n    xs.remove(max(xs))")]
    assert len(hb["no_len_guard"].apply(src)) == 2              # return i, return s.swapcase()
    extra, errs3 = compile_rules('''
rule noop_free
match: $a $o:Cmp $b
rewrite: $a < $b
  |
  $a <= $b

rule extend_in_if
match: $x.append($v)
where: parent("if $c: $*_")
rewrite: $x.extend([$v])

rule skip_doc
match: $S:Stmt
where: parent("def $f($*_):") and first() and not match($S, "$d:Const")
rewrite:
    pass
    $S
''')
    assert not errs3, errs3
    ex = {r.name: r for r in extra}
    assert ex["noop_free"].apply("y = x<1\n") == ["y = x <= 1\n"]
    assert ex["extend_in_if"].apply("if a:\n    l.append(1)\n") == ["if a:\n    l.extend([1])\n"]
    assert ex["skip_doc"].apply('def f():\n    "doc"\n    x = 1\n') == []
    closed, errs4 = compile_rules('''
rule use_total
match: return $e
where: not some($e, "total")
rewrite: return total
''')
    assert not errs4, errs4
    assert closed[0].apply("def f(xs):\n    return 0\n") == []          # no `total` in the program
    assert closed[0].apply("def f(xs):\n    total = sum(xs)\n    return 0\n") == [
        "def f(xs):\n    total = sum(xs)\n    return total\n"]
    from src.core.repair import single_site
    for r in rules:
        assert all(single_site(src, c) for c in r.apply(src)), r.name
    eff = lambda text: effect(compile_rules(text)[0][0])
    assert eff("rule a\nmatch: $X[1:].isupper()\nrewrite: (len($X) == 1 or $X[1:].isupper())\n") == (frozenset(), False)
    assert eff("rule b\nmatch: $X == []\nrewrite: $X = []\n") == ({"$X"}, False)       # binds $X: rescopes it
    assert eff("rule c\nmatch: $a = $x\nrewrite: $a = $x + 1\n") == (frozenset(), False)  # rebinds what it bound
    assert eff("rule d\nmatch: tmp = $x\nrewrite: print($x)\n") == ({"tmp"}, False)     # unbinds tmp
    assert eff("rule e\nmatch: print($x)\nrewrite: (yield $x)\n") == (frozenset(), True)  # turns a generator
    assert eff("rule f\nmatch: $f($x)\nrewrite: $f([y for y in $x])\n") == (frozenset(), False)
    print("rule language ok")

