"""Stage 2: synthesize a problem's repair tool (``tools/<p_id>/<model>/fixer.rules``).

The builder LLM is called **once per problem** with the problem and one worked
(buggy -> fixed) pair per cluster. It answers with a rule file in the rule
language (src/core/rulelang.py), which the engine interprets; no builder code
runs. The harness then *re-validates* the rules against the sample (a tool
cannot self-report success) and, if some samples are still uncovered or rules
were rejected, refines it — at most ``r_max`` builder calls total.

Build cost is exactly the tokens of those ``<= r_max`` calls, measured
uniformly through :mod:`src.utils.llm`. An ``llm_fn`` hook lets this run without
an API key in tests.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from src.core.cluster import cluster, cluster_docs, edit_script, pair_by_bfs
from src.core.repair import Rule, SearchBudget, repair
from src.prompts import render
from src.utils import llm as llm_mod

_TOOLS = Path(__file__).resolve().parents[2] / "tools"


# --------------------------------------------------------------- Stage-1 samples
def select_sample_pairs(buggy: list[str],
                        correct: list[str]) -> list[tuple[str, str, int]]:
    """One worked (buggy -> fixed) pair per cluster: the cluster's modal repair.

    ``k`` clusters produce ``k`` pairs. Nothing is capped, filtered or
    deduplicated, because every knob that used to trim this list was a guess and
    the build is too cheap for guessing to pay: showing a builder every cluster
    of every assignment costs a few dollars against the hundreds a
    per-submission arm spends on the same benchmark.

    Two choices here were measured rather than assumed:

    * **Representativeness** -- each cluster contributes its *modal* repair, the
      member whose edit script the cluster most agrees on. Neither obvious
      alternative survived: the medoid is the most typical *program*, usually a
      multi-issue mess, and the smallest repair is the submission that came
      closest to correct, an outlier rather than a spokesman.
    * **Grouping by repair, not by shape** -- clusters are built over the *edit
      script* between a program and its partner, not the program's own AST
      paths. A rule induced from a representative only pays off on members
      needing the same edit, so that is the partition to respect; grouping by
      shape reliably fills the largest clusters with programs that merely look
      alike.

    Each sample is paired with its minimum-edit correct program: sequences are
    matched one-to-one across top-level definitions and aligned, so the partner
    is the one needing the fewest operations rather than the one that merely
    looks closest. Showing the builder the pair -- buggy AND its targeted fix --
    turns "infer the fix, then generalize it" into "generalize this shown
    repair", which a weak model does far better. No LLM call: the fix is a real
    correct submission, picked locally.

    Returns ``(buggy, fixed, cluster_size)`` triples, cleanest repair first.
    """
    if not buggy:
        return []
    if not correct:
        clusters, _ = cluster(buggy)
        return [(buggy[c.medoid], "", len(c.members)) for c in clusters]

    partner, edit = pair_by_bfs(buggy, correct)
    docs = [edit_script(b, correct[int(partner[i])]) for i, b in enumerate(buggy)]
    # distance_threshold=None: cut where the data says, not at a constant.
    clusters, _ = (cluster_docs(docs, distance_threshold=None) if any(docs)
                   else cluster(buggy))

    picked = [(float(edit[c.medoid]), buggy[c.medoid],
               correct[int(partner[c.medoid])], len(c.members))
              for c in clusters]
    picked.sort(key=lambda t: t[0])                      # cleanest first
    return [(b, f, n) for _e, b, f, n in picked]


def load_fixer(path: str | Path) -> list[Rule]:
    """A builder's rule file (``fixer.rules``) in the rule language, plus the
    always-on operators written in the same language. No builder code runs."""
    from src.core.generic_rules import generic_rules
    from src.core.rulelang import compile_rules
    rules, errors = compile_rules(Path(path).with_suffix(".rules").read_text())
    if not rules and errors:
        raise ValueError("no rule compiled: " + "; ".join(errors[:5]))
    return [r.rule() for r in rules] + generic_rules()


# --------------------------------------------------------------- validation
def _validate(rules: list[Rule], problem: dict, samples: list[str],
              budget: SearchBudget):
    """Repair each sample once; return the per-sample RepairResults."""
    return [repair(b, problem, rules, budget) for b in samples]


# --------------------------------------------------------------- prompt inputs
def _render_tests(problem: dict, limit: int = 8) -> str:
    lines = []
    for t in (problem.get("tests") or [])[:limit]:
        if "stdin" in t:
            lines.append(f"- input {t['stdin']!r} -> {t['expected']!r}")
        else:
            entry = t.get("entry", problem.get("entry"))
            lines.append(f"- {entry}({', '.join(map(repr, t.get('args', [])))}) "
                         f"= {t.get('expected')!r}")
    return "\n".join(lines)


def _render_block(sources: list[str]) -> str:
    return "\n\n".join(f"```python\n{s.strip()}\n```" for s in sources)


def _render_pairs(samples: list[str], fixes: list[str]) -> str:
    """buggy → fixed pairs for the builder to generalize.

    Deliberately unannotated. Labelling each pair with its cluster size was
    tried and removed: the size is a property of our clustering, not of the
    class, and the audits show the largest clusters are the least coherent, so
    the count would assert most confidently exactly where it is least earned.
    """
    out = []
    for i, (b, f) in enumerate(zip(samples, fixes), 1):
        out.append(f"### Repair {i}\nBuggy:\n```python\n{b.strip()}\n```\n"
                   f"Fixed:\n```python\n{f.strip()}\n```")
    return "\n\n".join(out)


def _feedback(uncovered: list[str], load_error: str | None,
              rejected: list[str] | None = None) -> str:
    if rejected and not load_error:
        head = ("## This is a refinement round\n"
                "The engine rejected these rules of your previous file:\n"
                + "\n".join(f"- {e}" for e in rejected[:20])
                + "\nFix them and re-emit the whole rule file.")
        return head + ("\n\n" + _feedback(uncovered, None).split("\n", 1)[1] if uncovered else "")
    if load_error:
        return ("## This is a refinement round\n"
                "Your previous module failed to load:\n"
                f"```\n{load_error}\n```\nFix it and re-emit the whole module.")
    if not uncovered:
        return ""
    bugs = _render_block(uncovered)
    return ("## This is a refinement round\n"
            "Your previous module loaded but did NOT repair these sample "
            "submissions. Add or fix rules so they pass, keeping the ones that "
            f"already work:\n\n{bugs}")


def _rules_block(text: str | None) -> str | None:
    """The first fenced ``rules`` block of a response (or an untagged one)."""
    m = re.search(r"```(?:rules)?[ \t]*\n(.*?)```", text or "", re.S)
    return m.group(1).strip("\n") if m else None


# --------------------------------------------------------------- the build loop
@dataclass
class BuildResult:
    pid: str
    path: Path | None
    model: str = ""
    seconds: float = 0.0             # build wall-clock (ATT_build, per assignment)
    rules: int = 0
    coverage: float = 0.0            # fraction of sample bugs repaired
    rounds: int = 0
    in_tokens: int = 0
    out_tokens: int = 0
    usd: float = 0.0
    usd_paid: float | None = None     # billed, when batched at a discount
    n_samples: int = 0
    last_error: str | None = None
    provenance: list[list[str]] = field(default_factory=list)  # rules per sample

    def cost_record(self) -> dict:
        """What gets written to ``cost.json`` next to the tool — the audited
        build cost of this (problem, model) tool."""
        return {"pid": self.pid, "model": self.model, "rules": self.rules,
                "rounds": self.rounds, "n_samples": self.n_samples,
                "sample_coverage": round(self.coverage, 4),
                "in_tokens": self.in_tokens, "out_tokens": self.out_tokens,
                "usd": round(self.usd, 6),
                **({"usd_paid": round(self.usd_paid, 6)} if self.usd_paid is not None else {}),
                "build_seconds": round(self.seconds, 2)}


def build(problem: dict, samples: list[str],
          model: str = "claude-sonnet-5", r_max: int = 3, llm_fn=None,
          out_path: str | Path | None = None,
          budget: SearchBudget | None = None,
          sample_fixes: list[str] | None = None,
          batch: bool = False) -> BuildResult:
    """Generate–validate–refine a ``fixer.rules`` for one problem.

    ``sample_fixes[i]`` is a correct fix for ``samples[i]``; when given, the
    builder is shown (buggy → fixed) pairs to generalize, which a weak model
    handles far better than inferring the fix itself. The static semantics'
    rejections are fed back with the uncovered samples.
    """
    pid = problem["pid"]
    budget = budget or SearchBudget()
    out = Path(out_path) if out_path else _TOOLS / pid / model / "fixer.rules"
    out.parent.mkdir(parents=True, exist_ok=True)

    import time as _time
    _t0 = _time.time()
    res = BuildResult(pid=pid, path=None, model=model, n_samples=len(samples))
    uncovered_srcs: list[str] = []
    load_error: str | None = None
    rejected: list[str] = []
    best_code: str | None = None
    best_cov: float = -1.0
    call = llm_fn or llm_mod.complete
    # The builder emits a whole module, so the response needs generous headroom
    # or it truncates before the code block closes and the round is lost. At
    # 32768 that happened on every round of three assignments, costing $3.35 for
    # no tool, so the ceiling is the model's, not a guess. Only the real API
    # takes this kwarg (test stubs keep their (prompt, model) signature).
    out_cap = 64000
    extra = {} if llm_fn else {"max_tokens": out_cap, "batch": batch}

    sample_block = (_render_pairs(samples, sample_fixes) if sample_fixes
                    else _render_block(samples))
    for rnd in range(r_max):
        prompt = render("build_rules",
                        description=problem.get("description", ""),
                        tests=_render_tests(problem),
                        samples=sample_block,
                        feedback=_feedback(uncovered_srcs, load_error, rejected))
        comp = call(prompt, model=model, **extra)
        res.in_tokens += comp.in_tokens
        res.out_tokens += comp.out_tokens
        res.usd += comp.usd
        if getattr(comp, "usd_paid", None) is not None:
            res.usd_paid = (res.usd_paid or 0.0) + comp.usd_paid
        res.rounds = rnd + 1

        code = _rules_block(comp.text)
        if not code:
            # Truncation and refusal both arrive as "no code"; say which, or the
            # next round repeats the same over-long answer and is lost too.
            load_error = ("the previous answer was cut off at the output limit "
                          "before the code block closed -- write a shorter module"
                          if not llm_fn and comp.out_tokens >= out_cap
                          else "no rules code block in the response")
            res.last_error = load_error
            continue
        out.write_text(code)
        out.with_name(f"round{rnd + 1}.rules").write_text(code)   # for the static rejections

        try:
            from src.core.rulelang import compile_rules
            rejected = compile_rules(code)[1]
            rules = load_fixer(out)
        except Exception as e:                       # noqa: BLE001 - fed back
            load_error = f"{type(e).__name__}: {e}"
            res.last_error = load_error
            continue

        load_error = None
        results = _validate(rules, problem, samples, budget)
        cov = sum(r.repaired for r in results) / len(results) if results else 0.0
        if cov > best_cov:                           # keep the best round's tool,
            best_cov, best_code = cov, code          # not whichever ran last
            res.path = out
            res.rules = len(rules)
            res.coverage = cov
            res.provenance = [list(r.rules) for r in results]
        uncov_idx = [i for i, r in enumerate(results) if not r.repaired]
        if not uncov_idx:                            # all samples repaired
            break
        uncovered_srcs = [samples[i] for i in uncov_idx]

    res.seconds = _time.time() - _t0
    # A later round can regress or emit an unloadable module; persist the BEST
    # round's code, never whatever happened to run last (which may not parse).
    if best_code is not None:
        out.write_text(best_code)
    # Persist the audited build cost next to the tool (even if it never loaded,
    # so a failed build's spend is still on the record).
    (out.parent / "cost.json").write_text(json.dumps(res.cost_record(), indent=2))
    return res

