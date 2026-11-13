"""Export a Python module to a Surf s-expression, node for node as `ast` gives it.

Every node gets a label, 1, 2, ... in preorder; `Exporter.node[label]` is the node. Names,
constants, and attribute names are written as quoted strings; a constant is its `repr`. Nothing
is resolved, mangled, or rewritten here: scopes, mangling, and the translation are in Lean
(mech/Surf). Constructs the paper excludes (with, finally, match, async, except*, type
parameters) raise NotImplementedError.

    python3 -I export_surf.py FILE.py   -> the s-expression on standard output"""
import ast
import sys


def q(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


class Exporter:
    def __init__(self):
        self.n = 0
        self.node = {}
        self.label = {}

    def L(self, x):
        self.n += 1
        self.node[self.n] = x
        self.label[x] = self.n
        return self.n

    def o(self, x):                           # an optional expression
        return "()" if x is None else self.e(x)

    def es(self, xs):
        return "(" + " ".join(self.e(x) for x in xs) + ")"

    def params(self, a):
        pos = [*a.posonlyargs, *a.args]
        dflt = [None] * (len(pos) - len(a.defaults)) + list(a.defaults)
        out = []
        for i, x in enumerate(pos):
            out.append(self.param(x, "posonly" if i < len(a.posonlyargs) else "pos", dflt[i]))
        if a.vararg:
            out.append(self.param(a.vararg, "vararg", None))
        for x, d in zip(a.kwonlyargs, a.kw_defaults):
            out.append(self.param(x, "kwonly", d))
        if a.kwarg:
            out.append(self.param(a.kwarg, "kwarg", None))
        return "(" + " ".join(out) + ")"

    def param(self, x, kind, d):
        l = self.L(x)
        return f"(arg {l} {q(x.arg)} {kind} {self.o(d)} {self.o(x.annotation)})"

    def gen(self, g):
        if g.is_async:
            raise NotImplementedError("async comprehension")
        l = self.L(g)
        return f"(comprehension {l} {self.e(g.target)} {self.e(g.iter)} {self.es(g.ifs)})"

    def e(self, x):
        t = type(x).__name__
        l = self.L(x)
        if isinstance(x, ast.Constant):
            return f"(Constant {l} {q(repr(x.value))})"
        if isinstance(x, ast.Name):
            return f"(Name {l} {q(x.id)})"
        if isinstance(x, ast.BinOp):
            return f"(BinOp {l} {type(x.op).__name__} {self.e(x.left)} {self.e(x.right)})"
        if isinstance(x, ast.UnaryOp):
            return f"(UnaryOp {l} {type(x.op).__name__} {self.e(x.operand)})"
        if isinstance(x, ast.BoolOp):
            return f"(BoolOp {l} {type(x.op).__name__} {self.es(x.values)})"
        if isinstance(x, ast.Compare):
            ops = " ".join(type(o).__name__ for o in x.ops)
            return f"(Compare {l} {self.e(x.left)} ({ops}) {self.es(x.comparators)})"
        if isinstance(x, ast.IfExp):
            return f"(IfExp {l} {self.e(x.test)} {self.e(x.body)} {self.e(x.orelse)})"
        if isinstance(x, ast.Call):
            kws = []
            for k in x.keywords:
                lk = self.L(k)
                kws.append(f"(keyword {lk} {'()' if k.arg is None else q(k.arg)} {self.e(k.value)})")
            return f"(Call {l} {self.e(x.func)} {self.es(x.args)} ({' '.join(kws)}))"
        if isinstance(x, ast.Attribute):
            return f"(Attribute {l} {self.e(x.value)} {q(x.attr)})"
        if isinstance(x, ast.Subscript):
            return f"(Subscript {l} {self.e(x.value)} {self.e(x.slice)})"
        if isinstance(x, ast.Slice):
            return f"(Slice {l} {self.o(x.lower)} {self.o(x.upper)} {self.o(x.step)})"
        if isinstance(x, ast.Starred):
            return f"(Starred {l} {self.e(x.value)})"
        if isinstance(x, (ast.List, ast.Tuple, ast.Set)):
            return f"({t} {l} {self.es(x.elts)})"
        if isinstance(x, ast.Dict):
            items = " ".join(f"({self.o(k)} {self.e(v)})" for k, v in zip(x.keys, x.values))
            return f"(Dict {l} ({items}))"
        if isinstance(x, ast.Lambda):
            return f"(Lambda {l} {self.params(x.args)} {self.e(x.body)})"
        if isinstance(x, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            return f"({t} {l} {self.e(x.elt)} ({' '.join(self.gen(g) for g in x.generators)}))"
        if isinstance(x, ast.DictComp):
            return (f"(DictComp {l} {self.e(x.key)} {self.e(x.value)} "
                    f"({' '.join(self.gen(g) for g in x.generators)}))")
        if isinstance(x, ast.NamedExpr):
            return f"(NamedExpr {l} {q(x.target.id)} {self.e(x.value)})"
        if isinstance(x, ast.Yield):
            return f"(Yield {l} {self.o(x.value)})"
        if isinstance(x, ast.YieldFrom):
            return f"(YieldFrom {l} {self.e(x.value)})"
        if isinstance(x, ast.JoinedStr):
            return f"(JoinedStr {l} {self.es(x.values)})"
        if isinstance(x, ast.FormattedValue):
            return f"(FormattedValue {l} {self.e(x.value)} {x.conversion} {self.o(x.format_spec)})"
        raise NotImplementedError(t)

    def block(self, ss):
        return "(" + " ".join(self.s(s) for s in ss) + ")"

    def alias(self, a):
        l = self.L(a)
        return f"(alias {l} {q(a.name)} {'()' if a.asname is None else q(a.asname)})"

    def s(self, s):
        t = type(s).__name__
        if getattr(s, "type_params", None):
            raise NotImplementedError("type parameters")
        l = self.L(s)
        if isinstance(s, ast.Expr):
            return f"(Expr {l} {self.e(s.value)})"
        if isinstance(s, ast.Assign):
            return f"(Assign {l} {self.es(s.targets)} {self.e(s.value)})"
        if isinstance(s, ast.AugAssign):
            return f"(AugAssign {l} {self.e(s.target)} {type(s.op).__name__} {self.e(s.value)})"
        if isinstance(s, ast.AnnAssign):
            return f"(AnnAssign {l} {self.e(s.target)} {self.e(s.annotation)} {self.o(s.value)})"
        if isinstance(s, ast.Delete):
            return f"(Delete {l} {self.es(s.targets)})"
        if isinstance(s, ast.If):
            return f"(If {l} {self.e(s.test)} {self.block(s.body)} {self.block(s.orelse)})"
        if isinstance(s, ast.While):
            return f"(While {l} {self.e(s.test)} {self.block(s.body)} {self.block(s.orelse)})"
        if isinstance(s, ast.For):
            return (f"(For {l} {self.e(s.target)} {self.e(s.iter)} {self.block(s.body)} "
                    f"{self.block(s.orelse)})")
        if isinstance(s, (ast.Break, ast.Continue, ast.Pass)):
            return f"({t} {l})"
        if isinstance(s, ast.Return):
            return f"(Return {l} {self.o(s.value)})"
        if isinstance(s, ast.FunctionDef):
            return (f"(FunctionDef {l} {q(s.name)} {self.params(s.args)} {self.block(s.body)} "
                    f"{self.es(s.decorator_list)} {self.o(s.returns)})")
        if isinstance(s, ast.ClassDef):
            kws = []
            for k in s.keywords:
                lk = self.L(k)
                kws.append(f"(keyword {lk} {'()' if k.arg is None else q(k.arg)} {self.e(k.value)})")
            return (f"(ClassDef {l} {q(s.name)} {self.es(s.bases)} ({' '.join(kws)}) "
                    f"{self.block(s.body)} {self.es(s.decorator_list)})")
        if isinstance(s, (ast.Global, ast.Nonlocal)):
            return f"({t} {l} ({' '.join(q(x) for x in s.names)}))"
        if isinstance(s, ast.Try):
            if s.finalbody:
                raise NotImplementedError("finally")
            hs = []
            for h in s.handlers:
                lh = self.L(h)
                hs.append(f"(ExceptHandler {lh} {self.o(h.type)} {'()' if h.name is None else q(h.name)} "
                          f"{self.block(h.body)})")
            return f"(Try {l} {self.block(s.body)} ({' '.join(hs)}) {self.block(s.orelse)})"
        if isinstance(s, ast.Raise):
            return f"(Raise {l} {self.o(s.exc)} {self.o(s.cause)})"
        if isinstance(s, ast.Import):
            return f"(Import {l} ({' '.join(self.alias(a) for a in s.names)}))"
        if isinstance(s, ast.ImportFrom):
            m = "()" if s.module is None else q(s.module)
            return f"(ImportFrom {l} {m} ({' '.join(self.alias(a) for a in s.names)}) {s.level})"
        if isinstance(s, ast.Assert):
            return f"(Assert {l} {self.e(s.test)} {self.o(s.msg)})"
        raise NotImplementedError(t)

    def module(self, tree):
        return "(Module " + " ".join(self.s(s) for s in tree.body) + ")"


def export(src):
    """The s-expression of `src` and the exporter, whose `node` maps labels to nodes."""
    tree = ast.parse(src)
    x = Exporter()
    return x.module(tree), x, tree


if __name__ == "__main__":
    print(export(open(sys.argv[1]).read())[0])
