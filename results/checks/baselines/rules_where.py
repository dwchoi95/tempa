"""Where the builder's rules add small repairs (Section 6.2, Table D.2), from rows.csv
(analyze.py) and the stored TEMPA_L logs. No model call, no test run.
  - RR_0.25 without and with the rules: with no model (TEMPA_L), and TEMPA_LF at the
    default gate and at 0.25,
    per assignment, per corpus, and on the programs never shown as worked pairs;
  - on the unseen C1-C6 programs with no model, the same at tau 0.1, 0.25, 0.5, beside PyDex;
  - the programs the rules lose, and why;
  - recurrence: builder-rule repairs made by a rule that also repairs another program,
    and those programs whose edit script (Definition 3.2) no other program needs;
  - small builder-rule repairs the transplant alone also makes small.
    python3 results/checks/baselines/rules_where.py   -> rules_where.txt"""
import csv, json, math, sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.core.cluster import edit_script, pair_by_bfs      # noqa: E402
from src.experiments._common import IDS, ORDER, load_pool   # noqa: E402

HERE = Path(__file__).resolve().parent
CS1, M = ORDER[:5], ("claude-sonnet-5", "gpt-5.4-mini")
GATES = ("local", "+fallback", "+fallback gate 0.25")
csv.field_size_limit(10**9)
T = lambda v: v == "True"


def ok(r, tau=0.25):
    return T(r["held"]) and r["rps"] not in ("", "None") and float(r["rps"]) <= tau


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


def recurring(pid):
    """Definition 3.2: is b's edit script to its minimum-edit reference shared in the assignment?"""
    buggy, correct = load_pool(pid, "buggy"), load_pool(pid, "correct")
    part, _ = pair_by_bfs(buggy, correct)
    names = sorted(p.stem for p in (ROOT / "benchmark" / pid / "buggy").glob("*.py"))
    w = [edit_script(buggy[i], correct[int(part[i])]) for i in range(len(names))]
    c = Counter(w)
    return {(pid, b): c[w[i]] > 1 for i, b in enumerate(names)}


def main():
    out = []
    say = lambda *a: (print(*a), out.append(" ".join(map(str, a))))
    U = {(r["pid"], r["buggy"]) for r in csv.DictReader(open(HERE / "worked_pairs.csv"))
         if r["worked"] == "False"}
    rows = list(csv.DictReader(open(HERE / "rows.csv")))
    idx = {(r["arm"], r["pid"], r["model"], r["buggy"]): r for r in rows}
    keys = sorted({(r["pid"], r["buggy"]) for r in rows})
    groups = [(IDS[p], [k for k in keys if k[0] == p]) for p in ORDER]
    for tag, sub in (("", keys), ("unseen ", [k for k in keys if k in U])):
        groups += [(tag + "R1-R5", [k for k in sub if k[0] in CS1]),
                   (tag + "C1-C6", [k for k in sub if k[0] not in CS1]), (tag + "All", sub)]
    say("RR_0.25 without -> with rules (only with : only without, p, queries without -> with)")
    for name, ks in groups:
        cells = []
        for m in M:
            for g in GATES:
                a = [idx[(f"LLM rules | {g}", p, m, b)] for p, b in ks]
                c = [idx[(f"no rules | {g}", p, m, b)] for p, b in ks]
                x = sum(ok(i) and not ok(j) for i, j in zip(a, c))
                y = sum(ok(j) and not ok(i) for i, j in zip(a, c))
                q = (sum(T(j["query"]) for j in c), sum(T(i["query"]) for i in a))
                cells.append(f"{100 * sum(map(ok, c)) / len(ks):.1f}->{100 * sum(map(ok, a)) / len(ks):.1f} "
                             f"({x}:{y}, p={exact_p(x, y):.2g}, q {q[0]}->{q[1]})")
        say(f"{name:14}", " | ".join(cells))
    pydex = {(r["pid"], r["model"], r["buggy"]): r for r in csv.DictReader(open(HERE / "baseline_rows.csv"))
             if r["arm"] == "PyDex"}
    ks = [k for k in keys if k in U and k[0] not in CS1]
    say("\nunseen C1-C6, no model (TEMPA_L): small repairs, without -> with builder rules (x:y), and PyDex, per tau")
    for tau in (0.1, 0.25, 0.5):
        for m in M:
            a = [ok(idx[("LLM rules | local", p, m, b)], tau) for p, b in ks]
            c = [ok(idx[("no rules | local", p, m, b)], tau) for p, b in ks]
            say(f"tau {tau} {m}: {sum(c)} -> {sum(a)} ({sum(i and not j for i, j in zip(a, c))}:"
                f"{sum(j and not i for i, j in zip(a, c))}), PyDex {sum(ok(pydex[(p, m, b)], tau) for p, b in ks)} of {len(ks)}")
    say("\nprograms the rules lose: a larger rule repair before a smaller transplant?")
    for g in GATES:
        for m in M:
            why = Counter()
            for p, b in keys:
                a, c = idx[(f"LLM rules | {g}", p, m, b)], idx[(f"no rules | {g}", p, m, b)]
                if ok(c) and not ok(a):
                    why["preempted" if a["source"] == "rules" and T(a["held"]) and float(a["rps"]) > 0.25
                        else "other"] += 1
            say(g, m, dict(why))
    rec = {k: v for p in ORDER for k, v in recurring(p).items()}
    say("\nrecurrence and the transplant, builder-rule repairs (TEMPA_L)")
    for m in M:
        per_rule, used = defaultdict(set), {}
        for p in ORDER:
            for r in csv.DictReader(open(ROOT / "results" / p / "tempa_l.csv")):
                if r["Model"] == m and r["Source"] == "rules" and r["Fixed"] == "True":
                    used[(p, r["Buggy"])] = [n for n in json.loads(r["Rules_L"] or "[]") if not n.startswith("generic_")]
                    for n in used[(p, r["Buggy"])]:
                        per_rule[(p, n)].add(r["Buggy"])
        for corpus, inside in (("R1-R5", lambda p: p in CS1), ("C1-C6", lambda p: p not in CS1)):
            br = [k for k, ns in used.items() if ns and inside(k[0])]
            shared = [k for k in br if any(len(per_rule[(k[0], n)]) > 1 for n in used[k])]
            small = [(p, b) for p, b in keys if inside(p) and ok(idx[("LLM rules | local", p, m, b)])
                     and T(idx[("LLM rules | local", p, m, b)]["builder_rule"])]
            also = sum(ok(idx[("no rules | local", p, m, b)]) for p, b in small)
            say(m, corpus, f"builder-rule repairs {len(br)}; by a rule repairing another program {len(shared)} "
                f"({100 * len(shared) / len(br):.0f}%), of which edit script unique {sum(not rec[k] for k in shared)} "
                f"({100 * sum(not rec[k] for k in shared) / len(shared):.0f}%) [all: {100 * sum(not rec[k] for k in br) / len(br):.0f}%]; "
                f"small ones {len(small)}, transplant alone also small {also} ({100 * also / len(small):.0f}%)")
    (HERE / "rules_where.txt").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
