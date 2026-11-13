"""The syntax the buggy programs and every repair use, by AST node type, and calls that could
inspect code or frames. python3 -I syntax.py REPO   -> syntax.txt"""
import ast, csv, sys
from collections import Counter
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1])
ARMS = ("tempa_l", "tempa_lf", "refactory", "pydex", "direct_llm")
INSPECT = {"locals", "vars", "globals", "eval", "exec", "compile", "dir", "getattr", "setattr", "__import__"}
srcs = {}
for pid in sorted(p.parent.name for p in (REPO / "results").glob("*/tempa_l.csv")):
    for b in (REPO / "benchmark" / pid / "buggy").glob("*.py"):
        srcs[b.read_text()] = "buggy"
    for arm in ARMS:
        f = REPO / "results" / pid / f"{arm}.csv"
        if f.exists():
            for r in csv.DictReader(f.open()):
                if r["Fixed"] == "True" and r["Patch"]:
                    srcs.setdefault(r["Patch"], "repair")
node, prog, calls, mods = Counter(), Counter(), Counter(), Counter()
for s in srcs:
    try:
        t = ast.parse(s)
    except SyntaxError:
        prog["unparsable"] += 1
        continue
    prog["programs"] += 1
    seen = set()
    for n in ast.walk(t):
        seen.add(type(n).__name__)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in INSPECT:
            calls[n.func.id] += 1
        if isinstance(n, ast.Attribute) and n.attr.startswith("__") and n.attr.endswith("__"):
            calls[n.attr] += 1
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names:
                mods[(getattr(n, "module", None) or a.name).split(".")[0]] += 1
    node.update(seen)
keep = ("stmt", "expr")
out = [f"{prog}"]
out.append("node types by programs using them: " + ", ".join(f"{k} {v}" for k, v in sorted(node.items(), key=lambda x: -x[1])
                                                          if isinstance(getattr(ast, k, None), type) and issubclass(getattr(ast, k), (ast.stmt, ast.expr))))
out.append(f"inspection calls: {calls.most_common()}")
out.append(f"imports: {mods.most_common(20)}")
print("\n".join(out)); (Path(__file__).resolve().parent / "syntax.txt").write_text("\n".join(out) + "\n")
