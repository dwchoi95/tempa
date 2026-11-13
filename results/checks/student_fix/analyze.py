"""Hints against what the student actually changed. For a C1-C6 buggy submission whose author
later submitted a correct program of the class's pool, the student's own fix is the first such
program; the lines it changes are those of the buggy program that a line diff replaces or
removes, or next to which it inserts. A hint hits if it names one of them; precision and recall
are over the two sets of lines. Rows: every arm's repairs on those programs. No model call.
    python3 -I analyze.py REPO   -> analyze.txt, pairs.csv"""
import csv, difflib, math, statistics as st, sys
from collections import defaultdict
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core.footprint import footprint_lines     # noqa: E402
from src.experiments._common import ORDER          # noqa: E402
from src.utils.metrics import rps                  # noqa: E402
HERE = Path(__file__).resolve().parent
CF = [p for p in ORDER if p.startswith("cf_")]
M = ("claude-sonnet-5", "gpt-5.4-mini")
ARMS = (("tempa_l", "TEMPA_L"), ("tempa_lf", "TEMPA_LF"), ("pydex", "PyDex"), ("direct_llm", "LLM_Direct"), ("refactory", "Refactory"))


def changed(b, c):
    """Lines of b (1-based) that the line diff from b to c touches."""
    x = [l.strip() for l in b.splitlines()]
    y = [l.strip() for l in c.splitlines()]
    out = set()
    for tag, i1, i2, _j1, _j2 in difflib.SequenceMatcher(None, x, y, autojunk=False).get_opcodes():
        if tag in ("replace", "delete"):
            out.update(range(i1 + 1, i2 + 1))
        elif tag == "insert":
            out.update(k for k in (i1, i1 + 1) if 1 <= k <= len(x))
    return out


rows = list(csv.DictReader((HERE / "authors.csv").open()))
by = defaultdict(list)
for r in rows:
    by[(r["pid"], r["author"])].append(r)
pairs = []
for (pid, a), rs in by.items():
    kind = {f.stem: k for k in ("buggy", "correct") for f in (REPO / "benchmark" / pid / k).glob("*.py")}
    rs.sort(key=lambda r: int(r["time"]))
    for i, r in enumerate(rs):
        if kind[r["submission"]] != "buggy":
            continue
        nxt = next((s for s in rs[i + 1:] if kind[s["submission"]] == "correct"), None)
        if nxt:
            pairs.append((pid, r["submission"], nxt["submission"], int(nxt["time"]) - int(r["time"])))
print(len(rows), "submissions linked;", len(pairs), "buggy programs with the student's own later fix")
info = {}
for pid, b, c, dt in pairs:
    bs = (REPO / "benchmark" / pid / "buggy" / (b + ".py")).read_text()
    cs = (REPO / "benchmark" / pid / "correct" / (c + ".py")).read_text()
    info[(pid, b)] = dict(src=bs, ch=changed(bs, cs), rps=rps(bs, cs), dt=dt, fix=c)
with open(HERE / "pairs.csv", "w", newline="") as f:
    w = csv.writer(f); w.writerow(["pid", "buggy", "fix", "seconds", "student_rps", "changed_lines"])
    for (pid, b), v in sorted(info.items()):
        w.writerow([pid, b, v["fix"], v["dt"], round(v["rps"], 4), len(v["ch"])])
out = [f"{len(rows)} submissions linked; {len(info)} buggy programs with the student's own later fix; "
       f"student RPS median {st.median(v['rps'] for v in info.values()):.3f}; "
       f"changed lines median {st.median(len(v['ch']) for v in info.values())}"]
out.append("per problem: " + str({p: sum(k[0] == p for k in info) for p in CF}))


def stats(sub):
    res = {}
    for arm, name in ARMS:
        for m in M:
            got = {}
            for pid in CF:
                for r in csv.DictReader((REPO / "results" / pid / f"{arm}.csv").open()):
                    k = (pid, r["Buggy"])
                    if r["Model"] not in (m, "none") or k not in sub or r["Fixed"] != "True" or not r["Patch"]:
                        continue
                    try:
                        F = footprint_lines(sub[k]["src"], r["Patch"])
                    except SyntaxError:
                        continue
                    if F:
                        got[k] = dict(F=F, src=r["Source"], rps=float(r["RPS"]))
            res[(name, m)] = got
    return res


def line(label, got, sub):
    if not got:
        return f"  {label}: none"
    hit = [bool(v["F"] & sub[k]["ch"]) for k, v in got.items()]
    pr = [len(v["F"] & sub[k]["ch"]) / len(v["F"]) for k, v in got.items()]
    rc = [len(v["F"] & sub[k]["ch"]) / max(1, len(sub[k]["ch"])) for k, v in got.items()]
    return (f"  {label}: n {len(got)} hit {100 * st.mean(hit):.1f}% precision {100 * st.mean(pr):.1f}% "
            f"recall {100 * st.mean(rc):.1f}% hint lines {st.mean(len(v['F']) for v in got.values()):.1f} "
            f"rps {st.mean(v['rps'] for v in got.values()):.3f}")


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


for label, sub in (("all with a later fix", info),
                   ("student kept their program (student RPS <= 0.5)", {k: v for k, v in info.items() if v["rps"] <= .5}),
                   ("student's fix within a day", {k: v for k, v in info.items() if v["dt"] <= 86400})):
    out.append(f"\n== {label}: {len(sub)} programs")
    res = stats(sub)
    for (name, m), got in res.items():
        out.append(line(f"{name:10s} {m}", got, sub))
        if name == "TEMPA_L":
            out.append(line(f"  rules only {m}", {k: v for k, v in got.items() if v["src"] == "rules"}, sub))
    for m in M:
        a, b = res[("TEMPA_L", m)], res[("PyDex", m)]
        ru = {k: v for k, v in a.items() if v["src"] == "rules"}
        both = [k for k in ru if k in b]
        x = sum(len(ru[k]["F"] & sub[k]["ch"]) / len(ru[k]["F"]) > len(b[k]["F"] & sub[k]["ch"]) / len(b[k]["F"]) for k in both)
        y = sum(len(ru[k]["F"] & sub[k]["ch"]) / len(ru[k]["F"]) < len(b[k]["F"] & sub[k]["ch"]) / len(b[k]["F"]) for k in both)
        out.append(f"  rule hint vs PyDex by precision {m}: {x}:{y} of {len(both)}, p={exact_p(x, y):.2g}")
        for nm in ("PyDex", "Refactory", "LLM_Direct"):
            c = {k: res[(nm, m)][k] for k in ru if k in res[(nm, m)]}
            out.append(line(f"  {nm} on the same rule-repaired programs {m}", c, sub))
        out.append(line(f"  rules on the programs PyDex also repaired {m}", {k: ru[k] for k in both}, sub))
        chance = [len(sub[k]["ch"]) / max(1, len(sub[k]["src"].splitlines())) for k in ru]
        out.append(f"  chance on the rule-repaired programs {m}: a random line is one the student changed {100 * st.mean(chance):.1f}% of the time")
    allc = [len(v["ch"]) / max(1, len(v["src"].splitlines())) for v in sub.values()]
    out.append(f"  chance on all {len(sub)}: {100 * st.mean(allc):.1f}%")
print("\n".join(out)); (HERE / "analyze.txt").write_text("\n".join(out) + "\n")
