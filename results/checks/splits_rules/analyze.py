"""What the builder's own rules add when a tool is built from a class's first 10% and
repairs its last quarter (results/splits, run.py splits): per builder, on the pooled
test sets (R1-R5 x seeds 0-2, C1-C5 in submission order), RR_0.25 of the frozen tool
with rules and without, the repairs that use a rule the builder wrote, and LLM_Direct's
logged query on the same programs. The tool without rules was run once, under
claude-sonnet-5's T+, and serves both builders. Held-out as in results/checks/baselines. No model call.
    python3 results/checks/splits_rules/analyze.py   -> rows.csv, summary.csv
Each patch's held-out verdict is cached in heldout_cache.json (not tracked); without it, the
patches are run on the held-out suite again, which takes about 10 s."""
import csv, json, math, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.experiments import ablation                       # noqa: E402
from src.experiments._common import ORDER                  # noqa: E402
from src.experiments.augment import _suite                 # noqa: E402
from src.runner.testing import run_tests                   # noqa: E402

HERE = Path(__file__).resolve().parent
CS1 = ORDER[:5]
TAU = 0.25
csv.field_size_limit(10**9)


def builder_rule(v):
    return v["fixed"] and v["source"] == "rules" and any(
        not n.startswith("generic_") for n in json.loads(v["rules"] or "[]"))


def exact_p(a, b):
    n, k = a + b, min(a, b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


def main():
    cache_f = HERE / "heldout_cache.json"
    cache = json.loads(cache_f.read_text()) if cache_f.exists() else {}
    rows = []
    for scheme in ("s0", "s1", "s2"):
        for d in sorted((ROOT / "results/splits" / scheme / "f10").iterdir()):
            pid = d.name
            arms = {"rules": ablation._log(f"splits/{scheme}/f10/{pid}", "tempa_l")}
            # splits.py runs the tool without rules once, under the first builder's T+
            fw = ablation._log(f"splits/{scheme}/f10/{pid}", "tempa_l_fw")
            arms["no rules"] = {(m, b): fw[(next(iter(fw))[0], b)] for m, b in arms["rules"]}
            direct = ablation._log(pid, "direct_llm")
            arms["direct"] = {k: direct[k] for k in arms["rules"]}
            if pid in CS1:
                suite = _suite(pid)
                todo = sorted({v["patch"] for a in arms.values() for v in a.values()
                               if v["fixed"] and v["patch"] not in cache.get(pid, {})})
                with ThreadPoolExecutor(16) as ex:
                    got = dict(zip(todo, ex.map(lambda p: run_tests(p, suite).all_pass, todo)))
                cache.setdefault(pid, {}).update(got)
                cache_f.write_text(json.dumps(cache))
            for arm, a in arms.items():
                for (model, buggy), v in a.items():
                    held = v["fixed"] and (cache[pid][v["patch"]] if pid in CS1 else True)
                    rows.append({"scheme": scheme, "pid": pid, "corpus": "R" if pid in CS1 else "C",
                                 "model": model, "buggy": buggy, "arm": arm, "held": held,
                                 "ok": held and v["rps"] is not None and v["rps"] <= TAU,
                                 "builder_rule": builder_rule(v), "source": v["source"]})
            print(scheme, pid, flush=True)
    with open(HERE / "rows.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, rows[0].keys()); w.writeheader(); w.writerows(rows)
    idx = {(r["scheme"], r["pid"], r["model"], r["buggy"], r["arm"]): r for r in rows}
    out = []
    for model in sorted({r["model"] for r in rows}):
        # "distinct": a program in the test sets of several orders counts once, under its first order
        for corpus in ("all", "R", "C", "distinct"):
            keys = sorted({k[:4] for k in idx if k[2] == model and (corpus in ("all", "distinct") or idx[k]["corpus"] == corpus)})
            if corpus == "distinct":
                keys = sorted({k[1:]: k for k in reversed(keys)}.values())
            n = len(keys)
            ok = {a: sum(idx[k + (a,)]["ok"] for k in keys) for a in ("rules", "no rules", "direct")}
            x = sum(idx[k + ("rules",)]["ok"] and not idx[k + ("no rules",)]["ok"] for k in keys)
            y = sum(idx[k + ("no rules",)]["ok"] and not idx[k + ("rules",)]["ok"] for k in keys)
            bo = sum(idx[k + ("rules",)]["ok"] and idx[k + ("rules",)]["builder_rule"] for k in keys)
            out.append({"model": model, "corpus": corpus, "n": n,
                        **{f"RR25_{a}": round(100 * v / n, 1) for a, v in ok.items()},
                        "rules_only": x, "norules_only": y, "p": exact_p(x, y),
                        "ok_with_builder_rule": bo, "builder_rule_%": round(100 * bo / n, 1)})
            print(out[-1])
    with open(HERE / "summary.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, out[0].keys()); w.writeheader(); w.writerows(out)


if __name__ == "__main__":
    main()
