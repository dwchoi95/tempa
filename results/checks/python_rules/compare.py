"""Rules in the rule language against the same builders' rules as Python functions, on one engine
and one search (run_python.py), in the three builds. A repair counts as correct if it passes the
held-out suite on R1-R5 and the official tests on C1-C6. Small: correct with RPS <= 0.25. One line:
correct with a one-line hint. No model call. With `filter`, the Python arm is filter/run_filter.py's.
    python3 -I compare.py REPO [filter]   -> [filter/]compare.txt, compare.csv"""
import csv, json, math, statistics as st, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core.footprint import footprint_lines     # noqa: E402
from src.experiments._common import ORDER          # noqa: E402
from src.experiments.augment import _suite         # noqa: E402
from src.runner.testing import run_tests           # noqa: E402
HERE = REPO / "results/checks/python_rules"
ARM = HERE / "filter" if sys.argv[2:] == ["filter"] else HERE
M = ("claude-sonnet-5", "gpt-5.4-mini")
CS1 = ORDER[:5]
BUILDS = ("r0", "r1", "r2")
UNSEEN = {(r["pid"], r["buggy"]) for r in csv.DictReader(
    (REPO / "results/checks/baselines/worked_pairs.csv").open()) if r["worked"] == "False"}
cache_f = HERE / "heldout_cache.json"
cache = json.loads(cache_f.read_text()) if cache_f.exists() else {}


def path(form, b, pid):
    if form == "python":
        return ARM / "run" / b / pid / "tempa_l.csv"
    return REPO / ("results" if b == "r0" else f"results/rebuild/{b}") / pid / "tempa_l.csv"


def load(form, b):
    rows = {}
    for pid in ORDER:
        f = path(form, b, pid)
        if not f.exists():
            continue
        got = list(csv.DictReader(f.open()))
        if pid in CS1:
            suite = _suite(pid)
            c = cache.setdefault(pid, {})
            todo = sorted({r["Patch"] for r in got if r["Fixed"] == "True" and r["Patch"] not in c})
            with ThreadPoolExecutor(8) as ex:
                c.update(zip(todo, ex.map(lambda p: run_tests(p, suite).all_pass, todo)))
        for r in got:
            if r["Model"] not in M:
                continue
            k = (pid, r["Model"], r["Buggy"])
            fixed = r["Fixed"] == "True" and bool(r["Patch"])
            held = fixed and (cache[pid][r["Patch"]] if pid in CS1 else True)
            rps = float(r["RPS"]) if fixed and r["RPS"] not in ("", "None") else None
            F = None
            if fixed:
                src = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
                try:
                    F = footprint_lines(src, r["Patch"])
                except SyntaxError:
                    pass
            names = json.loads(r["Rules_L"] or "[]")
            rows[k] = dict(fixed=fixed, held=held, rps=rps, F=F, rule=fixed and r["Source"] == "rules",
                           builder=fixed and r["Source"] == "rules" and any(not n.startswith("generic_") for n in names),
                           small=held and rps is not None and rps <= .25,
                           one=held and F is not None and len(F) <= 1)
    return rows


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


SUB = (("all", lambda p, b: True), ("R1-R5", lambda p, b: p in CS1), ("C1-C6", lambda p, b: p not in CS1),
       ("unseen C1-C6", lambda p, b: p not in CS1 and (p, b) in UNSEEN))
data = {(f, b): load(f, b) for f in ("python", "language") for b in BUILDS}
cache_f.write_text(json.dumps(cache))
out, table = [], []
for label, sub in SUB:
    out.append(f"\n== {label}")
    for b in BUILDS:
        for m in M:
            d = {}
            for f in ("python", "language"):
                d[f] = {k: v for k, v in data[(f, b)].items() if k[1] == m and sub(k[0], k[2])}
            common = set(d["python"]) & set(d["language"])
            if not common:
                continue
            line = [f"{b} {m} n={len(common)}"]
            for f in ("python", "language"):
                v = [d[f][k] for k in common]
                ru = [x for x in v if x["rule"]]
                row = dict(subset=label, build=b, model=m, form=f, n=len(v), fixed=sum(x["fixed"] for x in v),
                           held=sum(x["held"] for x in v), rule=len(ru), builder=sum(x["builder"] for x in v),
                           rule_fail=sum(not x["held"] for x in ru), small=sum(x["small"] for x in v),
                           one=sum(x["one"] for x in v),
                           rule_rps=round(st.mean(x["rps"] for x in ru if x["rps"] is not None), 3) if ru else 0)
                table.append(row)
                line.append(f"{f}: fixed {row['fixed']} held {row['held']} rule {row['rule']} builder {row['builder']} "
                            f"rule_fail {row['rule_fail']} small {row['small']} one {row['one']} rps {row['rule_rps']}")
            for key in ("small", "one"):
                x = sum(d["language"][k][key] and not d["python"][k][key] for k in common)
                y = sum(d["python"][k][key] and not d["language"][k][key] for k in common)
                line.append(f"{key} language:python {x}:{y} p={exact_p(x, y):.2g}")
            out.append(" | ".join(line))
print("\n".join(out)); (ARM / "compare.txt").write_text("\n".join(out) + "\n")
with open(ARM / "compare.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(table[0])); w.writeheader(); w.writerows(table)
