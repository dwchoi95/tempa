"""Check Surf's classification, computed in Lean on Surf directly and through the translation
to PyCore (mech/Surf), against CPython 3.13's symbol tables.

Each program is exported node for node (export_surf.py); `pycore surf` prints, for every
occurrence of a name, its scope and classification as Surf's own analysis gives it (`socc`) and
as PyCore's analysis of the translated program gives it (`tocc`). Each occurrence in the source
is compared with CPython's symbol table of its scope, paired as translate_cls.py pairs them.
CPython 3.13 folds a list, set, or dict comprehension into the scope around it, where the
language reference makes it a nested function: inside one, a name its own generators bind is
local, a name an enclosing folded comprehension binds is free, a walrus target or any other name
is what CPython says of it in the scope around, a local of a function becoming free;
comprehensions in class bodies are skipped. A name that the scope around binds only as the
variable of another folded comprehension (CPython's DEF_COMP_ITER) is resolved above that scope
instead.

    python3 -I surf_cls.py REPO   -> surf_cls.txt (buggy programs and every stored repair)"""
import ast
import csv
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import translate_cls as T                     # noqa: E402
from export_surf import Exporter, export      # noqa: E402

csv.field_size_limit(10**9)
SCOPE = T.SCOPE


def mangle(name, sc, up, tree):
    """CPython's _Py_Mangle with the innermost class around scope `sc`."""
    if not name.startswith("__") or name.endswith("__") or "." in name:
        return name
    n = sc
    while n is not tree:
        if isinstance(n, ast.ClassDef):
            c = n.name.lstrip("_")
            return f"_{c}{name}" if c else name
        n = up[n]
    return name


def occurrences(tree, x, of, up):
    """(label, name, scope node, is walrus target) for every occurrence Surf reports."""
    out = []
    for l, n in x.node.items():
        if isinstance(n, ast.Name):
            out.append((l, n.id, of[n], False))
        elif isinstance(n, ast.NamedExpr):
            out.append((l, n.target.id, of[n.target], True))
        elif isinstance(n, ast.arg):
            out.append((l, n.arg, of[n], False))
        elif isinstance(n, (ast.FunctionDef, ast.ClassDef)):
            out.append((l, n.name, of[n], False))
        elif isinstance(n, ast.alias) and n.name != "*":
            out.append((l, n.asname or n.name.split(".")[0], of[n], False))
        elif isinstance(n, (ast.Global, ast.Nonlocal)):
            out += [(l, y, of[n], False) for y in n.names]
        elif isinstance(n, ast.ExceptHandler) and n.name:
            out.append((l, n.name, of[n], False))
    return out


def own_binds(c, up, tree):
    return {mangle(m.id, c, up, tree) for g in c.generators for m in ast.walk(g.target)
            if isinstance(m, ast.Name)}


def expected(src, tree, x):
    """(label, mangled name, scope label) -> CPython's 'local' | 'free' | 'global', or None to skip."""
    of, up, order = T.scopes(tree)
    tab, kept = T.tables(tree, src, up, order)
    out = {}
    for l, name, sc, walrus in occurrences(tree, x, of, up):
        name = mangle(name, sc, up, tree)
        key = (l, name, "module" if sc is tree else str(x.label[sc]))
        k = kept(sc)
        c = T.cpy(tab[k], name)
        if isinstance(sc, T.FOLD):
            if isinstance(k, ast.ClassDef):
                out[key] = None
                continue
            outer = set()
            n = up[sc]
            while isinstance(n, T.FOLD):
                outer |= own_binds(n, up, tree)
                n = up[n]
            if name in own_binds(sc, up, tree) and not walrus:
                c = "local"
            elif name in outer:
                c = "free"
            elif c == "local" and k is not tree:
                # bound in k only as the variable of another comprehension folded into it
                # (CPython 3.13's DEF_COMP_ITER): k does not bind it, so it resolves above k
                c = "free" if binds_k(tab, up, tree, k, name) else up_cls(tab, kept, up, tree, k, name)
        out[key] = c
    return out


DEF_COMP_ITER = 512                         # CPython 3.13 pycore_symtable.h: 2 << 8


def binds_k(tab, up, tree, k, name):
    """Whether the kept scope `k`, whose table has `name` local, binds it itself: not only as
    the variable of a comprehension folded into it (a generator expression's own variables
    are its own)."""
    if not tab[k].lookup(name)._Symbol__flags & DEF_COMP_ITER:
        return True
    return isinstance(k, ast.GeneratorExp) and name in own_binds(k, up, tree)


def up_cls(tab, kept, up, tree, k, name):
    """The classification of a name that scope `k` neither binds nor declares: free if the
    nearest enclosing function scope binds or declares it nonlocal, global otherwise."""
    n = kept(up[k])
    while n is not tree:
        if not isinstance(n, ast.ClassDef):
            try:
                s = tab[n].lookup(name)
            except KeyError:
                s = None
            if s is not None:
                if s.is_declared_global():
                    return "global"
                if (s.is_local() and binds_k(tab, up, tree, n, name)) or s.is_free() or s.is_nonlocal():
                    return "free"
        n = kept(up[n])
    return "global"


def lean(sxs, exe):
    """Run `pycore surf` on a batch; per program, (socc, tocc) dicts keyed like `expected`."""
    r = subprocess.run([str(exe), "surf"], input="\n".join(sxs), capture_output=True, text=True,
                       timeout=3600)
    if r.returncode:
        raise RuntimeError("lean: " + r.stderr[:300])
    res, cur = [], None
    for line in r.stdout.splitlines():
        w = line.split(" ")
        if w[0] == "prog":
            cur = ({}, {}, Counter(), [])
        elif w[0] == "end":
            res.append(cur)
        elif w[0] == "error":
            cur[3].append(line)
        elif w[0] in ("socc", "tocc"):
            d = cur[0] if w[0] == "socc" else cur[1]
            key = (int(w[1]), w[2], w[3])
            if key in d and d[key] != w[4]:
                cur[2][w[0] + " inconsistent"] += 1
            d[key] = w[4]
    if len(res) != len(sxs):
        raise RuntimeError("lean: lost programs")
    return res


IMPLICIT = {"__name__", "__module__", "__qualname__"}
COMPNAME = {ast.ListComp: "listcomp", ast.SetComp: "setcomp", ast.DictComp: "dictcomp",
            ast.GeneratorExp: "genexpr"}


def tables311(srcs):
    """CPython 3.11's symbol tables of each source (symtab311.py), or None where 3.11 cannot
    parse it."""
    py = os.environ.get("PYTHON311", "python3.11")
    r = subprocess.run([py, "-I", str(Path(__file__).resolve().parent / "symtab311.py")],
                       input="\n".join(json.dumps(s) for s in srcs), capture_output=True, text=True,
                       timeout=3600)
    if r.returncode:
        raise RuntimeError("python3.11: " + r.stderr[:300])
    out = [json.loads(l) for l in r.stdout.splitlines()]
    if len(out) != len(srcs):
        raise RuntimeError("python3.11: lost programs")
    return out


def expected311(tree, x, dump):
    """(label, mangled name, scope label) -> CPython 3.11's classification in the occurrence's own
    scope; a comprehension is a scope of its own there, as in the language reference."""
    of, up, order = T.scopes(tree)
    key = lambda n: ("lambda" if isinstance(n, ast.Lambda) else COMPNAME.get(type(n), getattr(n, "name", None)),
                     n.lineno)
    kids = {}
    for n in order:
        kids.setdefault(up[n], []).append(n)
    tab = {tree: dump}

    def pair(node):
        pool = {}
        for n in kids.get(node, []):
            pool.setdefault(key(n), []).append(n)
        for c in tab[node][3]:
            m = pool.get((c[0], c[1]))
            if not m:
                raise ValueError("unpaired scope (3.11)")
            n = m.pop(0)
            tab[n] = c
            pair(n)
    pair(tree)
    out = {}
    for l, name, sc, _ in occurrences(tree, x, of, up):
        name = mangle(name, sc, up, tree)
        out[(l, name, "module" if sc is tree else str(x.label[sc]))] = (
            "global" if sc is tree else tab[sc][2].get(name, "global"))
    return out


def compare(todo, exe, bad, nbad=40):
    """Counters per source of `todo` [(src, sx, expected)]: Lean's two classifications against
    CPython 3.13 (the folding rule above) and CPython 3.11."""
    res = []
    for i in range(0, len(todo), 500):
        part = todo[i:i + 500]
        dumps = tables311([p[0] for p in part])
        for (src, sx, exp), (s, t, inc, err), dump in zip(part, lean([p[1] for p in part], exe), dumps):
            c = Counter(inc)
            if err:
                c["lean error"] += 1
            e11 = None
            if dump is None:
                c["3.11 unparsable"] += 1
            else:
                try:
                    tree = ast.parse(src)
                    e11 = expected311(tree, export_labels(tree), dump)
                except ValueError:
                    c["3.11 unpaired"] += 1
            for key, want in exp.items():
                if want is None:
                    c["skipped (class-body comprehension)"] += 1
                    continue
                c["occurrences"] += 1
                for tag, d in (("surf", s), ("tr", t)):
                    got = d.get(key)
                    c[f"{tag} agree" if got == want else f"{tag} differ"] += 1
                    if got != want and len(bad) < nbad:
                        bad.append([tag, "3.13", key, want, got, src])
            if e11 is not None:
                for key, want in e11.items():
                    c["occurrences (3.11)"] += 1
                    if exp.get(key) not in (None, want):
                        c["3.13 rule vs 3.11 differ"] += 1
                    for tag, d in (("surf", s), ("tr", t)):
                        got = d.get(key)
                        c[f"{tag} agree (3.11)" if got == want else f"{tag} differ (3.11)"] += 1
                        if got != want and len(bad) < nbad:
                            bad.append([tag, "3.11", key, want, got, src])
            for tag, d in (("surf", s), ("tr", t)):
                extra = [k for k in d if k not in exp and k[1] not in IMPLICIT]
                c[f"{tag} lean-only occurrences"] += len(extra)
                if extra and len(bad) < nbad:
                    bad.append([tag, "lean-only", extra[:3], src])
                c[f"{tag} lean-only class dunders"] += sum(1 for k in d if k not in exp and k[1] in IMPLICIT)
            c["surf vs tr differ"] += sum(1 for k in set(s) | set(t) if s.get(k) != t.get(k))
            res.append(c)
    return res


def export_labels(tree):
    """The labels export() gives the nodes of `tree` (a fresh parse of the same source)."""
    x = Exporter()
    x.module(tree)
    return x


def prepare(src):
    tree = ast.parse(src)
    compile(src, "<p>", "exec")
    sx, x, tree = export(src)
    return sx, expected(src, tree, x)


def main(REPO):
    exe = Path(os.environ.get("PYCORE", REPO / "mech/.lake/build/bin/pycore"))
    jobs = [("buggy", f.read_text()) for f in sorted(REPO.glob("benchmark/*/buggy/*.py"))]
    arms = ("tempa_l", "tempa_lf", "tempa_l_fw", "pydex", "refactory", "direct_llm")
    fs = [f for a in arms for f in sorted((REPO / "results").glob(f"*/{a}.csv")) +
          sorted((REPO / "results/rebuild").glob(f"r*/*/{a}.csv"))]
    for f in fs:
        for r in csv.DictReader(f.open()):
            if r.get("Fixed") == "True" and r.get("Patch"):
                jobs.append(("repair", r["Patch"]))
    cache, todo = {}, []
    for kind, src in jobs:                   # distinct sources are exported and run once
        if src in cache:
            continue
        try:
            sx, exp = prepare(src)
        except SyntaxError:
            cache[src] = "unparsable"
            continue
        except (NotImplementedError, ValueError) as ex:
            cache[src] = "untranslated: " + str(ex)[:60]
            continue
        cache[src] = None
        todo.append((src, sx, exp))
    bad = []
    for (src, _, _), c in zip(todo, compare(todo, exe, bad)):
        cache[src] = c
    tot = {"buggy": Counter(), "repair": Counter()}
    for kind, src in jobs:
        r = cache[src]
        if isinstance(r, str):
            tot[kind][r] += 1
        else:
            tot[kind]["programs" if kind == "buggy" else "repairs"] += 1
            tot[kind].update(r)
    lines = [json.dumps({k: dict(sorted(v.items())) for k, v in tot.items()})] + [json.dumps(b) for b in bad]
    (Path(__file__).resolve().parent / "surf_cls.txt").write_text("\n".join(lines) + "\n")
    return lines


NAMES = ["a", "b", "x", "__p", "__q__"]
def gen_program(rng, depth=3):
    """A random module of nested functions, lambdas, classes, and comprehensions, with global,
    nonlocal, walrus, del, for, except-as, import, and augmented assignment; most do not compile
    and are dropped."""
    nm = lambda: rng.choice(NAMES)

    def expr(d, in_comp=False):
        r = rng.random()
        if d <= 0 or r < 0.35:
            return nm()
        if r < 0.5:
            return f"(lambda {nm()}, {nm()}={nm()}: {expr(d - 1)})"
        if r < 0.75:
            k = rng.choice(["[{} for {} in {}{}]", "({} for {} in {}{})", "{{{} for {} in {}{}}}"])
            cond = f" if {expr(d - 1, True)}" if rng.random() < 0.4 else ""
            more = f" for {nm()} in {expr(d - 1, True)}" if rng.random() < 0.3 else ""
            tgt = nm() if rng.random() < 0.7 else f"({nm()}, {nm()})"
            return k.format(expr(d - 1, True), tgt, expr(d - 1), more + cond)
        if r < 0.85:
            return f"({nm()} := {expr(d - 1, in_comp)})"
        return f"f({expr(d - 1, in_comp)}, k={nm()})"

    def body(d, ind, fn, outer=frozenset(), params=frozenset()):
        """`outer`: names bound in the function around, which a `nonlocal` may name;
        `params`: this function's parameters."""
        out, mine = [], set()
        p = " " * ind
        if fn and rng.random() < 0.5:        # declarations first, where they compile
            ok = sorted(outer - params)
            if ok and rng.random() < 0.6:
                out.append(f"{p}nonlocal {rng.choice(ok)}")
            else:
                out.append(f"{p}{rng.choice(['global', 'nonlocal'])} {nm()}")
        for _ in range(rng.randint(1, 4)):
            r = rng.random()
            if d > 0 and r < 0.2:
                f, a, b, c = nm(), nm(), nm(), nm()
                mine.add(f)
                out.append(f"{p}def {f}({a}, *{b}, {c}={expr(1)}):")
                out += body(d - 1, ind + 4, True, frozenset(mine | params) if fn else frozenset(),
                            frozenset({a, b, c}))
            elif d > 0 and r < 0.3:
                c = nm()
                mine.add(c)
                out.append(f"{p}class {c}({nm()}):")
                out += body(d - 1, ind + 4, False)
            elif r < 0.38 and fn:
                out.append(f"{p}{rng.choice(['global', 'nonlocal'])} {nm()}")
            elif r < 0.45:
                out.append(f"{p}del {nm()}")
            elif d > 0 and r < 0.52:
                a, b = nm(), nm()
                mine |= {a, b}
                out.append(f"{p}for {a}, {b} in {expr(1)}:")
                out += body(d - 1, ind + 4, fn, outer, params)
            elif d > 0 and r < 0.58:
                out.append(f"{p}try:")
                out += body(d - 1, ind + 4, fn, outer, params)
                e = nm()
                mine.add(e)
                out.append(f"{p}except {nm()} as {e}:")
                out += body(d - 1, ind + 4, fn, outer, params)
            elif r < 0.62:
                a = nm()
                mine.add(a)
                out.append(f"{p}import os as {a}")
            elif r < 0.68:
                a = nm()
                mine.add(a)
                out.append(f"{p}{a} += {expr(1)}")
            else:
                a = nm()
                mine.add(a)
                out.append(f"{p}{a} = {expr(depth)}")
        return out
    return "\n".join(body(depth, 0, False)) + "\n"


def fuzz(REPO, n, seed=0):
    """The same comparison on `n` random programs that compile."""
    import random
    import warnings
    warnings.simplefilter("ignore")
    exe = Path(os.environ.get("PYCORE", REPO / "mech/.lake/build/bin/pycore"))
    rng = random.Random(seed)
    todo = []
    while len(todo) < n:
        src = gen_program(rng)
        try:
            todo.append((src, *prepare(src)))
        except SyntaxError:
            continue
    bad = []
    c = Counter()
    for r in compare(todo, exe, bad, 20):
        c["programs"] += 1
        c.update(r)
    return c, bad


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[2] == "--fuzz":
        c, bad = fuzz(Path(sys.argv[1]), int(sys.argv[3]))
        lines = [json.dumps(dict(sorted(c.items())))] + [json.dumps(b) for b in bad]
        (Path(__file__).resolve().parent / "surf_cls_fuzz.txt").write_text("\n".join(lines) + "\n")
        print("\n".join(lines))
    else:
        print("\n".join(main(Path(sys.argv[1]))))
