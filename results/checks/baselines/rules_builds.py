"""The no-model gain of the rules on the C1-C6 programs never shown as worked pairs, in each
of the three builds (the campaign r0 and the rebuilds r1, r2, same data, prompts, and budgets),
per problem, and on the stricter unseen set that also drops exact texts of worked pairs.
Small: passes the official tests with RPS <= 0.25. No model call, no test run.
    python3 results/checks/baselines/rules_builds.py   -> rules_builds.txt"""
import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
CF = ["cf_1011B", "cf_10C", "cf_110A", "cf_11B", "cf_125A", "cf_131A"]
M = ("claude-sonnet-5", "gpt-5.4-mini")
csv.field_size_limit(10**9)
WP = list(csv.DictReader(open(HERE / "worked_pairs.csv")))
UNSEEN = {(r["pid"], r["buggy"]) for r in WP if r["worked"] == "False"}
STRICT = {(r["pid"], r["buggy"]) for r in WP if r["worked"] == "False" and r["text_dup"] == "False"}


def small(fixed, rps):
    return fixed == "True" and rps not in ("", "None") and float(rps) <= 0.25


def main():
    out = []
    say = lambda *a: (print(*a), out.append(" ".join(map(str, a))))
    base = {(r["pid"], r["model"], r["buggy"]): small(r["held"], r["rps"])
            for r in csv.DictReader(open(HERE / "rows.csv")) if r["arm"] == "no rules | local"}
    pydex = {(r["pid"], r["model"], r["buggy"]): small(r["held"], r["rps"])
             for r in csv.DictReader(open(HERE / "baseline_rows.csv")) if r["arm"] == "PyDex"}
    for name, ks in (("unseen", UNSEEN), ("unseen, no exact text of a worked pair", STRICT)):
        say(f"{name}: small repairs with no model (no builder rules | rules, per build r0 r1 r2 | PyDex)")
        for m in M:
            per = {p: [] for p in CF}
            tot = []
            for r in (0, 1, 2):
                n = 0
                for p in CF:
                    f = ROOT / ("results" if r == 0 else f"results/rebuild/r{r}") / p / "tempa_l.csv"
                    k = sum(small(x["Fixed"], x["RPS"]) for x in csv.DictReader(open(f))
                            if x["Model"] == m and (p, x["Buggy"]) in ks)
                    per[p].append(k)
                    n += k
                tot.append(n)
            sub = [k for k in ks if k[0] in CF]
            say(f"  {m}: n {len(sub)}; no builder rules {sum(base[(p, m, b)] for p, b in sub)}; "
                f"rules {tot}; PyDex {sum(pydex[(p, m, b)] for p, b in sub)}")
            for p in CF:
                say(f"    {p}: no builder rules {sum(base[(q, m, b)] for q, b in sub if q == p)}; rules {per[p]}")
    (HERE / "rules_builds.txt").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
