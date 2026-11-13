"""Check the mechanized classification against CPython on real programs.

Each program is translated to PyCore as Proposition 3.10 does, keeping what decides how names
resolve (scopes, binders, declarations); its meaning is not kept. The Lean executable
(mech/.lake/build/bin/pycore) classifies every occurrence of the translated program, and each
occurrence of a name in the source is compared with CPython 3.13's symbol tables.

CPython 3.13 folds a list, set, or dict comprehension into the scope around it, where the language
reference, and the translation, make it a nested function. Inside such a comprehension, a name it
binds is local, a walrus target and any other name are what CPython says of them in the scope
around, a local of a function becoming free; comprehensions in class bodies are skipped.

    python3 -I translate_cls.py REPO [GLOB]   -> lean_cls.txt"""
import ast
import csv
import json
import os
import subprocess
import symtable
import sys
from collections import Counter, defaultdict
from pathlib import Path

csv.field_size_limit(10**9)
FOLD = (ast.ListComp, ast.SetComp, ast.DictComp)
COMP = FOLD + (ast.GeneratorExp,)
DEF = (ast.FunctionDef, ast.AsyncFunctionDef)
SCOPE = DEF + (ast.Lambda, ast.ClassDef) + COMP


def _args(a):
    return [*a.posonlyargs, *a.args, *([a.vararg] if a.vararg else []), *a.kwonlyargs, *([a.kwarg] if a.kwarg else [])]


def scopes(tree):
    """node -> the scope (module, def, lambda, class, or comprehension node) it is evaluated in,
    and scope -> the scope around it. Decorators, defaults, annotations, bases, and a
    comprehension's first iterable belong to the scope around."""
    of, up, order = {}, {}, []

    def args(a, cur, fn):
        for d in a.defaults + [d for d in a.kw_defaults if d]:
            visit(d, cur)
        for x in _args(a):
            of[x] = fn
            if x.annotation:
                visit(x.annotation, cur)

    def enter(n, cur):
        up[n] = cur
        order.append(n)

    def visit(n, cur):
        of[n] = cur
        if isinstance(n, DEF):
            args(n.args, cur, n)
            for d in n.decorator_list:
                visit(d, cur)
            if n.returns:
                visit(n.returns, cur)
            enter(n, cur)
            for s in n.body:
                visit(s, n)
        elif isinstance(n, ast.Lambda):
            args(n.args, cur, n)
            enter(n, cur)
            visit(n.body, n)
        elif isinstance(n, ast.ClassDef):
            for x in n.bases + [k.value for k in n.keywords] + n.decorator_list:
                visit(x, cur)
            enter(n, cur)
            for s in n.body:
                visit(s, n)
        elif isinstance(n, COMP):
            g0 = n.generators
            visit(g0[0].iter, cur)
            enter(n, cur)
            for i, g in enumerate(g0):
                if i:
                    visit(g.iter, n)
                visit(g.target, n)
                for c in g.ifs:
                    visit(c, n)
            for el in ([n.key, n.value] if isinstance(n, ast.DictComp) else [n.elt]):
                visit(el, n)
        else:
            for c in ast.iter_child_nodes(n):
                visit(c, cur)
    visit(tree, tree)
    return of, up, order


def tables(tree, src, up, order):
    """Pair each scope that CPython keeps (not a folded comprehension) with its symbol table."""
    out = {tree: symtable.symtable(src, "<p>", "exec")}
    key = lambda n: ("lambda" if isinstance(n, ast.Lambda) else "genexpr" if isinstance(n, ast.GeneratorExp)
                     else n.name, n.lineno)

    def kept(n):                                # the nearest scope CPython keeps
        while isinstance(n, FOLD):
            n = up[n]
        return n
    kids = defaultdict(list)
    for n in order:
        if not isinstance(n, FOLD):
            kids[kept(up[n])].append(n)

    def pair(node):
        pool = defaultdict(list)
        for n in kids[node]:
            pool[key(n)].append(n)
        for t in out[node].get_children():
            k = (t.get_name(), t.get_lineno())
            if not pool[k]:
                raise ValueError("unpaired scope")
            m = pool[k].pop(0)
            out[m] = t
            pair(m)
    pair(tree)
    return out, kept


def cpy(t, name):
    if t.get_type() == "module":
        return "global"
    try:
        s = t.lookup(name)
    except KeyError:
        return "global"
    if s.is_declared_global() or s.is_global():
        return "global"
    if s.is_free() or s.is_nonlocal():
        return "free"
    if s.is_local() or s.is_parameter():
        return "local"
    return "global"


def mangle(name, scope, up):
    if not name.startswith("__") or name.endswith("__"):
        return name
    n = scope
    while n in up and up[n] is not n:
        if isinstance(n, ast.ClassDef) and n.name.lstrip("_"):
            return f"_{n.name.lstrip('_')}{name}"
        n = up[n]
    return name


class T:
    """Translation to the Lean executable's input. Source occurrences get labels 1..; fresh
    nodes get labels from 10**6 on and are never compared. Private names are mangled as the
    compiler does."""

    def __init__(self, up, of):
        self.up, self.of = up, of
        self.fresh, self.n, self.occ, self.pre = 10**6, 0, {}, []

    def L(self):
        self.fresh += 1
        return self.fresh

    def nm(self, node, name):
        return json.dumps(mangle(name, self.of[node], self.up))

    def src(self, node, name, tag=""):
        self.n += 1
        self.occ[(self.n, mangle(name, self.of[node], self.up))] = (node, tag)
        return self.n

    def tmp(self):
        return f'"_t{self.L()}"'

    def chain(self, parts):
        out = f"(const {self.L()} 0)"
        for p in parts:
            out = f"(bin {self.L()} op {out} {p})"
        return out

    # expressions; ctx is "fn", "mod", "cls", or "lam" (an expression-only scope)
    def e(self, x, ctx):
        if isinstance(x, ast.Name):
            return f"(name {self.src(x, x.id)} {self.nm(x, x.id)})" if isinstance(x.ctx, ast.Load) else f"(const {self.L()} 0)"
        if isinstance(x, ast.NamedExpr):
            return f"(walrus {self.src(x.target, x.target.id)} {self.nm(x.target, x.target.id)} {self.e(x.value, ctx)})"
        if isinstance(x, ast.Lambda):
            t = self.tmp()
            outer = [self.e(d, ctx) for d in x.args.defaults + [d for d in x.args.kw_defaults if d]]
            binds = [f"(walrus {self.src(a, a.arg)} {self.nm(a, a.arg)} (name {self.L()} {t}))" for a in _args(x.args)]
            body = self.chain(binds + [self.e(x.body, "lam")])
            return self.chain(outer + [f"(lambda {self.L()} {t} {body})"])
        if isinstance(x, COMP):
            return self.comp(x, ctx)
        return self.chain([self.e(c, ctx) for c in _exprs(x)])

    def comp(self, x, ctx):
        first = self.e(x.generators[0].iter, ctx)
        walrus = sorted({w.target.id for w in ast.walk(x) if isinstance(w, ast.NamedExpr) and self._owner(w) is x})
        parts, t = [], self.tmp()
        for i, g in enumerate(x.generators):
            if i:
                parts.append(self.e(g.iter, "lam"))
            parts += self.texpr(g.target)
            parts += [self.e(c, "lam") for c in g.ifs]
        parts += [self.e(el, "lam") for el in ([x.key, x.value] if isinstance(x, ast.DictComp) else [x.elt])]
        if not walrus:
            return f"(call {self.L()} (lambda {self.L()} {t} {self.chain(parts)}) {first})"
        if ctx not in ("fn", "mod"):
            raise NotImplementedError("walrus comprehension in an expression scope")
        c = self.tmp()
        fn = self.of[x] if ctx == "fn" else None
        decl = [f"({'nonlocal' if fn is not None and not _declares(fn, y, ast.Global) else 'global'} {self.L()} {json.dumps(y)})" for y in walrus]
        self.pre.append(f"(def {self.L()} {c} {t} ({' '.join(decl)} (expr {self.L()} {self.chain(parts)})))")
        if fn is not None:                      # a dead assignment keeps the target local
            self.pre += [f"(if {self.L()} (const {self.L()} 0) ((assign {self.L()} {json.dumps(y)} (const {self.L()} 0))) ())"
                         for y in walrus if not _declares(fn, y, ast.Global) and not _declares(fn, y, ast.Nonlocal)]
        return f"(call {self.L()} (name {self.L()} {c}) {first})"

    def _owner(self, w):                        # the comprehension a walrus binds through, if any
        n = self.of[w]
        return n if isinstance(n, COMP) else None

    def texpr(self, tg):                        # a comprehension target, bound by walrus
        if isinstance(tg, ast.Name):
            return [f"(walrus {self.src(tg, tg.id)} {self.nm(tg, tg.id)} (const {self.L()} 0))"]
        if isinstance(tg, (ast.Tuple, ast.List)):
            return [p for el in tg.elts for p in self.texpr(el.value if isinstance(el, ast.Starred) else el)]
        return [self.e(tg, "lam")]

    # statements
    def target(self, tg, val, ctx):
        if isinstance(tg, ast.Name):
            return [f"(assign {self.src(tg, tg.id)} {self.nm(tg, tg.id)} {val})"]
        if isinstance(tg, (ast.Tuple, ast.List)):
            out = [f"(expr {self.L()} {val})"]
            for el in tg.elts:
                out += self.target(el.value if isinstance(el, ast.Starred) else el, f"(const {self.L()} 0)", ctx)
            return out
        return [f"(expr {self.L()} {self.chain([val, self.e(tg, ctx)])})"]

    def body(self, ss, ctx):
        saved, out = self.pre, []
        for s in ss:
            self.pre = []
            got = self.s(s, ctx)
            out += self.pre + got
        self.pre = saved
        return f"({' '.join(out) or f'(expr {self.L()} (const {self.L()} 0))'})"

    def s(self, s, ctx):
        L, e = self.L, self.e
        if isinstance(s, DEF):
            outer = [f"(expr {L()} {e(d, ctx)})" for d in s.args.defaults + [d for d in s.args.kw_defaults if d] + s.decorator_list]
            outer += [f"(expr {L()} {e(a.annotation, ctx)})" for a in _args(s.args) if a.annotation]
            outer += [f"(expr {L()} {e(s.returns, ctx)})"] if s.returns else []
            t = self.tmp()
            binds = " ".join(f"(assign {self.src(a, a.arg)} {self.nm(a, a.arg)} (name {L()} {t}))" for a in _args(s.args))
            return outer + [f"(def {self.src(s, s.name)} {self.nm(s, s.name)} {t} ({binds} {self.body(s.body, 'fn')[1:-1]}))"]
        if isinstance(s, ast.ClassDef):
            outer = [f"(expr {L()} {e(x, ctx)})" for x in s.bases + [k.value for k in s.keywords] + s.decorator_list]
            return outer + [f"(class {self.src(s, s.name)} {self.nm(s, s.name)} {self.body(s.body, 'cls')})"]
        if isinstance(s, ast.Return):
            return [f"(return {L()} {e(s.value, ctx) if s.value else f'(const {L()} 0)'})"]
        if isinstance(s, ast.Delete):
            return [f"(del {self.src(x, x.id)} {self.nm(x, x.id)})" if isinstance(x, ast.Name) else f"(expr {L()} {e(x, ctx)})"
                    for x in s.targets]
        if isinstance(s, ast.Assign):
            out, v = [], e(s.value, ctx)
            for tg in s.targets:
                out += self.target(tg, v, ctx)
                v = f"(const {L()} 0)"
            return out
        if isinstance(s, ast.AugAssign):
            if isinstance(s.target, ast.Name):
                x = s.target
                r = f"(name {self.src(x, x.id)} {self.nm(x, x.id)})"
                return [f"(assign {self.src(x, x.id, 'store')} {self.nm(x, x.id)} (bin {L()} op {r} {e(s.value, ctx)}))"]
            return [f"(expr {L()} {self.chain([e(s.target, ctx), e(s.value, ctx)])})"]
        if isinstance(s, ast.AnnAssign):
            out = [f"(expr {L()} {e(s.annotation, ctx)})"] if ctx != "fn" else []
            return out + self.target(s.target, e(s.value, ctx) if s.value else f"(const {L()} 0)", ctx)
        if isinstance(s, (ast.For, ast.AsyncFor)):
            loop = self.target(s.target, f"(const {L()} 0)", ctx)
            out = [f"(expr {L()} {e(s.iter, ctx)})", f"(while {L()} (const {L()} 1) ({' '.join(loop)} {self.body(s.body, ctx)[1:-1]}))"]
            return out + ([f"(if {L()} (const {L()} 1) {self.body(s.orelse, ctx)} ())"] if s.orelse else [])
        if isinstance(s, ast.While):
            out = [f"(while {L()} {e(s.test, ctx)} {self.body(s.body, ctx)})"]
            return out + ([f"(if {L()} (const {L()} 1) {self.body(s.orelse, ctx)} ())"] if s.orelse else [])
        if isinstance(s, ast.If):
            return [f"(if {L()} {e(s.test, ctx)} {self.body(s.body, ctx)} {self.body(s.orelse, ctx) if s.orelse else '()'})"]
        if isinstance(s, (ast.With, ast.AsyncWith)):
            out = []
            for it in s.items:
                out.append(f"(expr {L()} {e(it.context_expr, ctx)})")
                if it.optional_vars is not None:
                    out += self.target(it.optional_vars, f"(const {L()} 0)", ctx)
            return out + [f"(if {L()} (const {L()} 1) {self.body(s.body, ctx)} ())"]
        if isinstance(s, ast.Raise):
            return [f"(raise {L()} {self.chain([e(x, ctx) for x in (s.exc, s.cause) if x])})"]
        if isinstance(s, (ast.Try, ast.TryStar)):
            out = [f"(if {L()} (const {L()} 1) {self.body(s.body, ctx)} ())"]
            for h in s.handlers:
                lx, x = (self.src(h, h.name), self.nm(h, h.name)) if h.name else (L(), self.tmp())
                ty = e(h.type, ctx) if h.type else f"(const {L()} 0)"
                out.append(f"(try {L()} ((expr {L()} (const {L()} 0))) {lx} {ty} {x} {self.body(h.body, ctx)})")
            return out + [f"(if {L()} (const {L()} 1) {self.body(b, ctx)} ())" for b in (s.orelse, s.finalbody) if b]
        if isinstance(s, (ast.Import, ast.ImportFrom)):
            return [f"(assign {self.src(a, n)} {json.dumps(n)} (const {L()} 0))"
                    for a in s.names if a.name != "*" for n in [(a.asname or a.name).split(".")[0]]]
        if isinstance(s, ast.Global):
            return [f"(global {self.src(s, x)} {self.nm(s, x)})" for x in s.names]
        if isinstance(s, ast.Nonlocal):
            return [f"(nonlocal {self.src(s, x)} {self.nm(s, x)})" for x in s.names]
        if isinstance(s, (ast.Expr, ast.Assert)):
            return [f"(expr {L()} {e(x, ctx)})" for x in ([s.value] if isinstance(s, ast.Expr) else [s.test, s.msg]) if x]
        if isinstance(s, (ast.Pass, ast.Break, ast.Continue)):
            return [f"(expr {L()} (const {L()} 0))"]
        raise NotImplementedError(type(s).__name__)


def _exprs(x):
    for c in ast.iter_child_nodes(x):
        if isinstance(c, ast.expr):
            yield c
        elif isinstance(c, ast.keyword):
            yield c.value
        elif not isinstance(c, (ast.expr_context, ast.operator, ast.boolop, ast.unaryop, ast.cmpop)):
            yield from _exprs(c)


def _declares(fn, y, kind):
    stack = list(fn.body)
    while stack:
        n = stack.pop()
        if isinstance(n, kind) and y in n.names:
            return True
        if not isinstance(n, DEF + (ast.ClassDef, ast.Lambda)):
            stack += list(ast.iter_child_nodes(n))
    return False


def expected(src, tree, occ, of, up, order):
    """(label, name) -> CPython's 'local' | 'free' | 'global', or None to skip."""
    tab, kept = tables(tree, src, up, order)
    out = {}
    for (l, name), (node, tag) in occ.items():
        sc = of[node]
        k = kept(sc)
        c = cpy(tab[k], name)
        if isinstance(sc, FOLD):
            if isinstance(k, ast.ClassDef):
                out[(l, name)] = None
                continue
            binds = {m.id for f in _fold_chain(sc, up) for g in f.generators for m in ast.walk(g.target) if isinstance(m, ast.Name)}
            walrus_target = isinstance(node, ast.Name) and isinstance(of.get(node), FOLD) and any(
                isinstance(w, ast.NamedExpr) and w.target is node for w in ast.walk(sc))
            if name in binds and not walrus_target:
                c = "local"
            elif c == "local" and k is not tree:
                c = "free"
        out[(l, name)] = c
    return out


def _fold_chain(sc, up):
    while isinstance(sc, FOLD):
        yield sc
        sc = up[sc]


def check(src, exe):
    tree = ast.parse(src)
    compile(src, "<p>", "exec")
    of, up, order = scopes(tree)
    tr = T(up, of)
    sx = f"(module {tr.body(tree.body, 'mod')[1:-1]})"
    exp = expected(src, tree, tr.occ, of, up, order)
    r = subprocess.run([str(exe)], input=sx, capture_output=True, text=True, timeout=60)
    got = {}
    for line in r.stdout.splitlines():
        w = line.split(" ")
        if w[0] == "occ":
            got[(int(w[1]), json.loads(w[2]) if w[2].startswith('"') else w[2])] = w[4]
    if r.returncode or not got:
        raise RuntimeError("lean: " + r.stderr[:200])
    return exp, got


def main(REPO, pat):
    exe = Path(os.environ.get("PYCORE", REPO / "mech/.lake/build/bin/pycore"))
    tot, bad = Counter(), []
    for f in sorted(REPO.glob(pat)):
        try:
            exp, got = check(f.read_text(), exe)
        except SyntaxError:
            tot["unparsable"] += 1
            continue
        except (NotImplementedError, ValueError, RuntimeError) as ex:
            tot["untranslated: " + str(ex)[:60]] += 1
            continue
        tot["programs"] += 1
        for k, c in exp.items():
            if c is None:
                tot["skipped (class-body comprehension)"] += 1
                continue
            tot["occurrences"] += 1
            if got.get(k) == c:
                tot["agree"] += 1
            else:
                tot["differ"] += 1
                if len(bad) < 30:
                    bad.append([str(f.relative_to(REPO)), k[0], k[1], c, got.get(k)])
    return tot, bad


if __name__ == "__main__":
    REPO = Path(sys.argv[1])
    tot, bad = main(REPO, sys.argv[2] if len(sys.argv) > 2 else "benchmark/*/buggy/*.py")
    lines = [json.dumps(dict(sorted(tot.items())))] + [json.dumps(b) for b in bad]
    print("\n".join(lines))
    (Path(__file__).resolve().parent / "lean_cls.txt").write_text("\n".join(lines) + "\n")


def repairs(REPO):
    """The same check on every stored repair of every arm (results/*/ARM.csv, rebuilds included)."""
    exe = Path(os.environ.get("PYCORE", REPO / "mech/.lake/build/bin/pycore"))
    arms = ("tempa_l", "tempa_lf", "tempa_l_fw", "pydex", "refactory", "direct_llm")
    fs = [f for a in arms for f in sorted((REPO / "results").glob(f"*/{a}.csv")) + sorted((REPO / "results/rebuild").glob(f"r*/*/{a}.csv"))]
    tot, bad = Counter(), []
    for f in fs:
        for r in csv.DictReader(f.open()):
            if r.get("Fixed") != "True" or not r.get("Patch"):
                continue
            try:
                exp, got = check(r["Patch"], exe)
            except SyntaxError:
                tot["unparsable"] += 1
                continue
            except (NotImplementedError, ValueError, RuntimeError) as ex:
                tot["untranslated: " + str(ex)[:60]] += 1
                continue
            tot["repairs"] += 1
            for k, c in exp.items():
                if c is None:
                    tot["skipped (class-body comprehension)"] += 1
                    continue
                tot["occurrences"] += 1
                if got.get(k) == c:
                    tot["agree"] += 1
                else:
                    tot["differ"] += 1
                    if len(bad) < 30:
                        bad.append([str(f.relative_to(REPO)), r.get("Buggy"), k[0], k[1], c, got.get(k)])
    lines = [json.dumps(dict(sorted(tot.items())))] + [json.dumps(b) for b in bad]
    (Path(__file__).resolve().parent / "lean_cls_repairs.txt").write_text("\n".join(lines) + "\n")
    return lines
