"""The engine's one-hole splice, on which the rule language (src/core/rulelang.py) runs.

For a program p, a node n of p, an expression or a statement other than a
definition (def, async def, class), and a text t, ``substitute`` returns p with
n replaced by what t parses to: an expression for an expression, zero or more
statements for a statement. It keeps a candidate only when its AST is exactly
p's with that one subtree (or that one statement, widened to a run of
statements) replaced, so a rule cannot touch a second position: the single-site
contract holds by construction of the language rather than by a check on what a
rule returns.

``Ctx`` gives read-only access to the program: ctx.text(node) is a node's source
text, ctx.parent(node) its parent, ctx.field(node) the field of the parent it
sits in, and ctx.tree the whole module.
"""
from __future__ import annotations

import ast
import re


class Ctx:
    def __init__(self, source: str, tree: ast.AST):
        self.source, self.tree = source, tree
        self._parent: dict[int, tuple[ast.AST, str]] = {}
        for p in ast.walk(tree):
            for f, v in ast.iter_fields(p):
                for c in (v if isinstance(v, list) else [v]):
                    if isinstance(c, ast.AST):
                        self._parent[id(c)] = (p, f)
        lines = source.splitlines(keepends=True)
        self._starts = [0]
        for ln in lines:
            self._starts.append(self._starts[-1] + len(ln))

    def span(self, node: ast.AST) -> tuple[int, int]:
        return (self._starts[node.lineno - 1] + node.col_offset,
                self._starts[node.end_lineno - 1] + node.end_col_offset)

    def text(self, node: ast.AST) -> str:
        s, e = self.span(node)
        return self.source[s:e]

    def parent(self, node: ast.AST) -> ast.AST | None:
        return self._parent.get(id(node), (None, None))[0]

    def field(self, node: ast.AST) -> str | None:
        return self._parent.get(id(node), (None, None))[1]


_CTX = re.compile(r"ctx=(?:Load|Store|Del)\(\)")
_HOLE = "__tempa_hole__"
_DEFS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)   # never a hole


def _dump(t) -> str:
    """ast.dump without expression contexts (Load/Store/Del), which the parser
    derives from where a node sits rather than from what it says."""
    if isinstance(t, list):
        return "[" + ", ".join(_dump(x) for x in t) + "]"
    return _CTX.sub("", ast.dump(t))


def _path(ctx: "Ctx", node: ast.AST) -> list:
    """Field/index steps from the module down to node, via the parent map."""
    steps = []
    while True:
        up = ctx._parent.get(id(node))
        if up is None:
            return steps[::-1]
        parent, f = up
        v = getattr(parent, f)
        steps.append((f, next(i for i, x in enumerate(v) if x is node)
                      if isinstance(v, list) else None))
        node = parent


def _holed(tree: ast.AST, path: list, k: int = 1):
    """(dump of tree with the node at path, or the run of k list elements
    there, replaced by one sentinel; what that hole held). None if the path
    does not exist in tree. The tree is restored before returning."""
    try:
        node = tree
        for f, i in path[:-1]:
            node = getattr(node, f) if i is None else getattr(node, f)[i]
        f, i = path[-1]
        hole = ast.Name(id=_HOLE, ctx=ast.Load())
        if i is None:
            old = getattr(node, f)
            setattr(node, f, hole)
            try:
                return _dump(tree), old
            finally:
                setattr(node, f, old)
        seq = getattr(node, f)
        if i + k > len(seq):
            return None
        old = seq[i:i + k]
        seq[i:i + k] = [hole]
        try:
            return _dump(tree), old
        finally:
            seq[i:i + 1] = old
    except (AttributeError, IndexError, TypeError):
        return None


def substitute(source: str, tree: ast.AST, ctx: Ctx, node: ast.AST, text: str,
               _outside: dict | None = None) -> str | None:
    """source with node replaced by text, or None if text does not parse as
    the same kind of node or the splice would change anything else. A
    candidate is kept only if it parses to tree with exactly that subtree (or
    that statement, widened to a run of statements) replaced."""
    path = _path(ctx, node)
    if not path:
        return None
    outside = (_outside if _outside is not None else {}).get(id(node))
    if outside is None:
        outside = _holed(tree, path)[0]
        if _outside is not None:
            _outside[id(node)] = outside
    s, e = ctx.span(node)

    def accept(cand: str, new, k: int) -> bool:
        try:
            got = _holed(ast.parse(cand), path, k)
        except SyntaxError:
            return False
        return got is not None and got[0] == outside and _dump(got[1]) == _dump(new)

    if isinstance(node, ast.expr):
        try:
            new = ast.parse(text.strip(), mode="eval").body
        except SyntaxError:
            return None
        for t in (text.strip(), f"({text.strip()})"):   # parenthesize only if needed
            cand = source[:s] + t + source[e:]
            if accept(cand, new if path[-1][1] is None else [new], 1):
                return cand
        return None
    if isinstance(node, ast.stmt) and path[-1][1] is not None:
        try:
            new = ast.parse(text).body
        except SyntaxError:
            return None
        line_start = source.rfind("\n", 0, s) + 1
        indent = source[line_start:s]
        if not new:                            # deletion: drop the statement's lines
            siblings = getattr(ctx.parent(node), path[-1][0])
            if len(siblings) == 1:             # an emptied block keeps a `pass`
                cand = source[:s] + "pass" + source[e:]
                return cand if accept(cand, [ast.Pass()], 1) else None
            line_end = source.find("\n", e)
            cand = source[:line_start] + (source[line_end + 1:] if line_end >= 0 else "")
            return cand if accept(cand, [], 0) else None
        body = text.strip("\n").splitlines()
        cand = source[:s] + ("\n" + indent).join(body) + source[e:]
        return cand if accept(cand, new, len(new)) else None
    return None


if __name__ == "__main__":                     # the splice's own check
    from src.core.repair import single_site
    src = "def f(a, b, c):\n    if a < b:\n        return a * b\n    return c\n"
    tree = ast.parse(src)
    ctx = Ctx(src, tree)
    nodes = list(ast.walk(tree))

    def at(pred, text):
        return substitute(src, tree, ctx, next(n for n in nodes if pred(n)), text)
    got = [at(lambda n: isinstance(n, ast.Compare), "a <= b"),
           at(lambda n: isinstance(n, ast.BinOp), "a + b"),
           at(lambda n: isinstance(n, ast.Name) and n.id == "a"
              and isinstance(ctx.parent(n), ast.BinOp), "a + c"),
           at(lambda n: isinstance(n, ast.Return) and isinstance(n.value, ast.Name),
              "if c is None:\n    return 0\nreturn c"),
           at(lambda n: isinstance(n, ast.Return) and isinstance(n.value, ast.BinOp), "")]
    assert got[0] == src.replace("a < b", "a <= b")
    assert got[1] == src.replace("a * b", "a + b")
    assert got[2] == src.replace("a * b", "(a + c) * b")              # parenthesized
    assert "    if c is None:\n        return 0\n    return c" in got[3], got[3]
    assert "pass" in got[4]                                           # emptied block
    assert at(lambda n: isinstance(n, ast.Compare), "a <") is None   # does not parse
    assert all(single_site(src, c) for c in got)
    print("splice ok")
