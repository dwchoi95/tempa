"""The hint of every returned repair (src/core/footprint.py), from the stored logs and
run.py's cache (without cache/, it runs run.py first), and ../baselines/rows.csv (from
../baselines/analyze.py); no model call, no execution.
  - per source of TEMPA_LF's repairs, and per baseline: repairs, hint size in lines,
    hints that reach beyond the edited sites;
  - completeness: inputs on which the repair changed the outcome, and those on which the
    buggy program ran through no line of the hint (a timeout on either side is left out);
  - programs with a correct repair whose hint has at most 1, 2, 3 lines, per arm, and,
    for one line on the unseen C1-C6 programs, paired tests, rebuilds, and problems;
  - the effect: rule repairs by scope-neutral rules alone, whose hint needs no analysis,
    and those whose full footprint differs from their edited sites.
    python3 -I footprint_lines.py REPO   -> footprint_lines.txt"""
import csv, hashlib, json, math, statistics as st, sys
from collections import defaultdict
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.core import rulelang                                  # noqa: E402
from src.core.footprint import footprint_lines                 # noqa: E402
from src.core.synthesis import load_fixer                      # noqa: E402
from src.experiments._common import ORDER, tool_path           # noqa: E402
HERE = Path(__file__).resolve().parent
ARMS = (("tempa_lf", "TEMPA_LF"), ("pydex", "PyDex"), ("refactory", "Refactory"), ("direct_llm", "LLM_Direct"))
M = ("claude-sonnet-5", "gpt-5.4-mini")
sha = lambda s: hashlib.sha1(s.encode()).hexdigest()[:16]
if not any((HERE / "cache").glob("*.jsonl")):   # run.py's executions (1.4 GB, not tracked): make them first
    import subprocess; subprocess.run([sys.executable, "-I", str(HERE / "run.py"), str(REPO)], check=True)
runs = {}
for f in sorted((HERE / "cache").glob("*.jsonl")):
    for l in f.open():
        d = json.loads(l); runs[(f.stem, d["sha"])] = d.get("runs")
neutral = {(p, m): {r.name: r.neutral for r in load_fixer(REPO / tool_path(p, m))} for p in ORDER for m in M}
agg = defaultdict(lambda: defaultdict(int)); sizes = defaultdict(list)
for arm, name in ARMS:
    for pid in ORDER:
        for r in csv.DictReader((REPO / "results" / pid / f"{arm}.csv").open()):
            if r["Fixed"] != "True" or not r["Patch"]:
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            try:
                F, S = footprint_lines(b, r["Patch"]), footprint_lines(b, r["Patch"], sites_only=True)
            except SyntaxError:
                continue
            for m in (M if r["Model"] == "none" else (r["Model"],)):
                key = (name, r["Source"] if arm == "tempa_lf" else "", m)
                a = agg[key]; a["repairs"] += 1
                a["whole"] += F is None
                a["beyond"] += F is None or F != S
                if F is not None:
                    sizes[key].append(len(F))
                if r["Source"] == "rules":
                    ns = json.loads(r["Rules_L"] or "[]")
                    if ns and all(neutral[(pid, m)].get(n, False) for n in ns):
                        a["neutral"] += 1
                        a["neutral_beyond"] += F != S
                rb, rc = runs.get((pid, sha(b))), runs.get((pid, sha(r["Patch"])))
                if not rb or not rc or len(rb) != len(rc):
                    a["no_runs"] += 1
                    continue
                for x, y in zip(rb, rc):
                    if '"t": 1' in x["o"] or '"t": 1' in y["o"] or x["o"] == y["o"]:
                        continue
                    a["changed"] += 1
                    if F is not None and not set(x["L"]) & F:
                        a["missed"] += 1
                    if not set(x["L"]) & S:
                        a["missed_by_sites"] += 1
out = []
for k in sorted(agg):
    a, s = agg[k], sorted(sizes[k])
    out.append(f"{k[0]:10s} {k[1]:9s} {k[2]:16s} repairs {a['repairs']:5d}  beyond the edit {a['beyond']:3d} "
               f"(whole {a['whole']})  hint lines mean {st.mean(s):.1f} median {st.median(s):.0f} "
               f"<=1 {100 * sum(x <= 1 for x in s) / len(s):.0f}% <=2 {100 * sum(x <= 2 for x in s) / len(s):.0f}% "
               f"<=3 {100 * sum(x <= 3 for x in s) / len(s):.0f}%  changed {a['changed']} missed {a['missed']} "
               f"missed by the edited lines {a['missed_by_sites']}  no runs {a['no_runs']}"
               + (f"  neutral {a['neutral']} of them beyond {a['neutral_beyond']}" if k[1] == "rules" else ""))


def correct(arm):
    """{(pid, model, buggy): whether the arm's repair passes the held-out or official tests}."""
    f, col = ((REPO / "results/checks/baselines/rows.csv", "arm") if "|" in arm
              else (REPO / "results/checks/baselines/baseline_rows.csv", "arm"))
    return {(r["pid"], r["model"], r["buggy"]): r["held"] == "True" for r in csv.DictReader(f.open()) if r[col] == arm}


UNSEEN = {(r["pid"], r["buggy"]) for r in csv.DictReader(
    (REPO / "results/checks/baselines/worked_pairs.csv").open()) if r["worked"] == "False"}
CS1 = ORDER[:5]
ROWS = (("no builder rules, no model", "tempa_l_fw", "no rules | local"), ("TEMPA_L", "tempa_l", "LLM rules | local"),
        ("TEMPA_LF", "tempa_lf", "LLM rules | +fallback"), ("PyDex", "pydex", "PyDex"),
        ("LLM_Direct", "direct_llm", "LLM_Direct"), ("Refactory", "refactory", "Refactory"))
out.append("\nprograms with a correct repair whose hint has at most 1, 2, 3 lines")
for label, sub in (("all 2,970", lambda p, b: True), ("unseen C1-C6", lambda p, b: p not in CS1 and (p, b) in UNSEEN),
                   ("R1-R5", lambda p, b: p in CS1), ("C1-C6", lambda p, b: p not in CS1)):
    for name, arm, key in ROWS:
        ok, cells = correct(key), []
        for m in M:
            n, c = 0, [0, 0, 0]
            for pid in ORDER:
                for r in csv.DictReader((REPO / "results" / pid / f"{arm}.csv").open()):
                    if r["Model"] not in (m, "none") or not sub(pid, r["Buggy"]):
                        continue
                    n += 1
                    if r["Fixed"] != "True" or not r["Patch"] or not ok.get((pid, m, r["Buggy"])):
                        continue
                    b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
                    try:
                        F = footprint_lines(b, r["Patch"])
                    except SyntaxError:
                        continue
                    for i in range(3):
                        c[i] += F is not None and len(F) <= i + 1
            cells.append(f"{m}: n {n} {c}")
        out.append(f"{label:13s} {name:27s} " + " | ".join(cells))


def one_line(arm, key, m, ks, root="results"):
    """{(pid, buggy)}: programs of ks with a correct repair whose hint is one line."""
    ok, got = correct(key) if key else None, set()
    for pid in sorted({p for p, _ in ks}):
        for r in csv.DictReader((REPO / root / pid / f"{arm}.csv").open()):
            if r["Model"] not in (m, "none") or (pid, r["Buggy"]) not in ks or r["Fixed"] != "True" or not r["Patch"]:
                continue
            if ok is not None and not ok.get((pid, m, r["Buggy"])):
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            try:
                F = footprint_lines(b, r["Patch"])
            except SyntaxError:
                continue
            if F is not None and len(F) <= 1:
                got.add((pid, r["Buggy"]))
    return got


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


ks = {k for k in UNSEEN if k[0] not in CS1}
out.append("\nunseen C1-C6: programs with a correct repair and a one-line hint, paired (x:y, exact McNemar)")
for m in M:
    x, y, z = (one_line("tempa_l", "LLM rules | local", m, ks), one_line("tempa_l_fw", "no rules | local", m, ks),
               one_line("pydex", "PyDex", m, ks))
    out.append(f"{m}: TEMPA_L {len(x)}; without builder rules {len(y)} ({len(x - y)}:{len(y - x)}, p={exact_p(len(x - y), len(y - x)):.2g}); "
               f"PyDex {len(z)} ({len(x - z)}:{len(z - x)}, p={exact_p(len(x - z), len(z - x)):.2g}); "
               f"rebuilds {[len(one_line('tempa_l', None, m, ks, f'results/rebuild/r{r}')) for r in (1, 2)]}")
    per = {p: (sum(k[0] == p for k in y), sum(k[0] == p for k in x)) for p in sorted({k[0] for k in ks})}
    out.append(f"  per problem without -> with builder rules: {per}")


out.append("\nrule repairs against PyDex's on the programs both repaired, by hint lines (shorter:longer, exact sign test)")
for m in M:
    py, x, y = {}, 0, 0
    for pid in ORDER:
        py.update({(pid, r["Buggy"]): r["Patch"] for r in csv.DictReader((REPO / "results" / pid / "pydex.csv").open())
                   if r["Model"] == m and r["Fixed"] == "True" and r["Patch"]})
    for pid in ORDER:
        for r in csv.DictReader((REPO / "results" / pid / "tempa_l.csv").open()):
            if r["Model"] != m or r["Source"] != "rules" or r["Fixed"] != "True" or (pid, r["Buggy"]) not in py:
                continue
            b = (REPO / "benchmark" / pid / "buggy" / (r["Buggy"] + ".py")).read_text()
            try:
                F, G = footprint_lines(b, r["Patch"]), footprint_lines(b, py[(pid, r["Buggy"])])
            except SyntaxError:
                continue
            if F is not None and G is not None:
                x += len(F) < len(G); y += len(F) > len(G)
    out.append(f"{m}: {x}:{y}, p={exact_p(x, y):.2g}")
print("\n".join(out)); (HERE / "footprint_lines.txt").write_text("\n".join(out) + "\n")
