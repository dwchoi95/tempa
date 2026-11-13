"""What the programs of the differential run use: called names, methods, attributes, imports,
operators, float sources. python3 -I census.py REPO -> census.txt"""
import ast, builtins, sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from progs import programs

REPO = Path(sys.argv[1])
C = {k: Counter() for k in ("names", "methods", "attrs", "imports", "ops", "float", "misc", "dunder_defs", "decorators")}
progs_using = Counter()
B = set(dir(builtins))
for pid, kind, src in programs(REPO):
    try:
        t = ast.parse(src)
    except SyntaxError:
        C["misc"]["unparsable"] += 1
        continue
    seen = set()
    for n in ast.walk(t):
        if isinstance(n, ast.Call):
            if isinstance(n.func, ast.Name):
                C["names"][n.func.id] += 1; seen.add("call:" + n.func.id)
            elif isinstance(n.func, ast.Attribute):
                C["methods"][n.func.attr] += 1; seen.add("meth:" + n.func.attr)
        elif isinstance(n, ast.Attribute):
            C["attrs"][n.attr] += 1; seen.add("attr:" + n.attr)
        if isinstance(n, ast.Name) and n.id in B and isinstance(n.ctx, ast.Load):
            seen.add("bname:" + n.id)
        if isinstance(n, ast.Import):
            for a in n.names: C["imports"][a.name] += 1; seen.add("imp:" + a.name)
        if isinstance(n, ast.ImportFrom):
            for a in n.names: C["imports"][f"{n.module}.{a.name}"] += 1; seen.add(f"imp:{n.module}.{a.name}")
        if isinstance(n, (ast.BinOp, ast.AugAssign)):
            C["ops"][type(n.op).__name__] += 1; seen.add("op:" + type(n.op).__name__)
        if isinstance(n, ast.UnaryOp):
            C["ops"]["u" + type(n.op).__name__] += 1
        if isinstance(n, ast.Compare):
            for o in n.ops: C["ops"][type(o).__name__] += 1; seen.add("op:" + type(o).__name__)
        if isinstance(n, ast.Constant) and isinstance(n.value, float):
            C["float"]["literal"] += 1; seen.add("float")
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Div):
            seen.add("float")
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "float":
            seen.add("float")
        if isinstance(n, ast.FunctionDef):
            if n.name.startswith("__"): C["dunder_defs"][n.name] += 1
            for d in n.decorator_list: C["decorators"][ast.unparse(d)] += 1
        if isinstance(n, ast.ClassDef):
            seen.add("class")
            for d in n.decorator_list: C["decorators"][ast.unparse(d)] += 1
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Mod) and isinstance(n.left, (ast.Constant, ast.JoinedStr)) and isinstance(getattr(n.left, "value", None), str):
            seen.add("percent-format")
        # `__annotations__` by name, attribute or string (the always-present SETUP_ANNOTATIONS of
        # the translation is unobservable without it or introspection)
        if (isinstance(n, ast.Name) and n.id == "__annotations__") or \
                (isinstance(n, ast.Attribute) and n.attr == "__annotations__") or \
                (isinstance(n, ast.Constant) and n.value == "__annotations__"):
            seen.add("annotations-name")
        if isinstance(n, ast.Call) and n.keywords:
            for k in n.keywords:
                if isinstance(n.func, ast.Name): C["misc"][f"kw {n.func.id}({k.arg}=)"] += 1
                elif isinstance(n.func, ast.Attribute): C["misc"][f"kw .{n.func.attr}({k.arg}=)"] += 1
    progs_using.update(seen)
out = []
for k, c in C.items():
    out.append(f"== {k}: " + ", ".join(f"{a} {b}" for a, b in c.most_common()))
out.append("== programs using: " + ", ".join(f"{a} {b}" for a, b in progs_using.most_common()))
out.append("== programs naming __annotations__: " + str(progs_using["annotations-name"]) +
           "; introspecting (vars, dir, locals, globals, __dict__): " +
           str(sum(progs_using[k] for k in ("call:vars", "call:dir", "call:locals", "call:globals", "attr:__dict__"))))
(Path(__file__).resolve().parent / "census.txt").write_text("\n".join(out) + "\n")
print("\n".join(o[:3000] for o in out))
