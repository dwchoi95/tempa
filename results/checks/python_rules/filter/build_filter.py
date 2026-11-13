"""The Python-rule build loop of commit f3fde1df~1, with the language's checks as a filter inside it
(common.py): each round's rejected rules stay out of the tool and their reasons go back to the
builder in the words the rule language uses, so the two loops differ only in what the builder writes.
    python3 results/checks/python_rules/filter/build_filter.py BUILD PID MODEL
        -> tools/BUILD/PID/MODEL/{fixer.py, rejected.json, cost.json}"""
import json, string, sys, time
from pathlib import Path
import common                                      # noqa: F401 - maps src.core.rewrite first
from common import HERE, ROOT, check, rewrites
from src.core.generic_rules import generic_rules
from src.core.repair import SearchBudget, repair
from src.core.synthesis import _render_block, _render_pairs, _render_tests, select_sample_pairs
from src.experiments._common import load_env, load_pool, load_problem
from src.utils import llm as llm_mod
R_MAX, OUT_CAP = 3, 64000


def feedback(uncovered, load_error, rejected):
    if load_error:
        return ("## This is a refinement round\nYour previous module failed to load:\n"
                f"```\n{load_error}\n```\nFix it and re-emit the whole module.")
    parts = []
    if rejected:
        parts.append("The engine rejected these rules of your previous module:\n"
                     + "\n".join(f"- {e}" for e in rejected[:20]) + "\nFix them and re-emit the whole module.")
    if uncovered:
        parts.append("Your previous module loaded but did NOT repair these sample submissions. Add or fix "
                     f"rules so they pass, keeping the ones that already work:\n\n{_render_block(uncovered)}")
    return "## This is a refinement round\n" + "\n\n".join(parts) if parts else ""


def main(build, pid, model):
    load_env()
    d = HERE / "tools" / build / pid / model
    if (d / "cost.json").exists():
        return
    d.mkdir(parents=True, exist_ok=True)
    root = "benchmark" if build == "r0" else f"rebuild_work/{build}"
    problem = load_problem(pid, root)
    pairs = select_sample_pairs(load_pool(pid, "buggy", root), load_pool(pid, "correct", root))
    samples, fixes = [b for b, _f, _n in pairs], [f for _b, f, _n in pairs]
    template, budget, t0 = (HERE / "build_rewrites.md").read_text(), SearchBudget(), time.time()
    usd = tin = tout = rounds = 0
    best, best_cov, uncovered, load_error, rejected, written = None, -1.0, [], None, [], 0
    for rnd in range(R_MAX):
        prompt = string.Formatter().vformat(template, (), dict(
            description=problem.get("description", ""), tests=_render_tests(problem),
            samples=_render_pairs(samples, fixes), feedback=feedback(uncovered, load_error, rejected)))
        comp = llm_mod.complete(prompt, model=model, max_tokens=OUT_CAP)
        usd, tin, tout, rounds = usd + comp.usd, tin + comp.in_tokens, tout + comp.out_tokens, rnd + 1
        code = comp.code
        if not code:
            load_error = ("the previous answer was cut off at the output limit before the code block closed "
                          "-- write a shorter module" if comp.out_tokens >= OUT_CAP
                          else "no python code block in the response")
            continue
        if "import Rule" not in code:
            code = "from src.core.repair import Rule\n" + code
        (d / "fixer.py").write_text(code)
        (d / f"round{rnd + 1}.py").write_text(code)
        try:
            got = rewrites(d / "fixer.py")
        except Exception as e:                     # noqa: BLE001 - fed back
            load_error = f"{type(e).__name__}: {e}"
            continue
        load_error, written = None, written + len(got)
        verdicts = [(r, check(r, samples)) for r in got]
        rejected = [why for _r, why in verdicts if why]
        kept = [r.rule() for r, why in verdicts if not why]
        results = [repair(b, problem, kept + generic_rules(), budget) for b in samples]
        cov = sum(r.repaired for r in results) / len(results) if results else 0.0
        if cov > best_cov:
            best_cov = cov
            best = dict(code=code, rules=len(kept), rejected=[r.name for r, why in verdicts if why],
                        reasons=rejected)
        uncovered = [s for s, r in zip(samples, results) if not r.repaired]
        if not uncovered and not rejected:
            break
    if best:
        (d / "fixer.py").write_text(best["code"])
        (d / "rejected.json").write_text(json.dumps(dict(names=best["rejected"], reasons=best["reasons"]), indent=1))
    (d / "cost.json").write_text(json.dumps(dict(
        pid=pid, model=model, rules=best and best["rules"], rounds=rounds, written=written, n_samples=len(samples),
        sample_coverage=round(max(best_cov, 0.0), 4), in_tokens=tin, out_tokens=tout, usd=round(usd, 6),
        build_seconds=round(time.time() - t0, 2)), indent=2))
    print(pid, build, model, "rules", best and best["rules"], "rejected", best and len(best["rejected"]),
          "coverage", round(best_cov, 3), "rounds", rounds, f"${usd:.4f}")


if __name__ == "__main__":
    main(*sys.argv[1:4])
