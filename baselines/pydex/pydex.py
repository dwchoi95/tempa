"""PyDex baseline — reproduction of the *semantic phase* of
Zhang et al., "PyDex: Repairing Bugs in Introductory Python Assignments using
LLMs" (OOPSLA 2024), driven by our own models through ``src.utils.llm`` so
token/latency/cost accounting is uniform across arms.

Faithful mechanics (per the paper's Sec. 4.2 and Figs. 6-7):

* **Prompt** — the multimodal zero-shot prompt of Fig. 6, laid out exactly as
  shown: the buggy program FIRST, then the natural-language description, then
  the instructor test cases, closing with ``### Correct Program ###``.
* **K candidates** — each prompt yields up to ``K = 10`` candidates, issued
  as parallel sampled calls (the paper's Codex n=10 was a single request, so a
  deployment's wall-clock is one round trip, not ten): ``seconds`` is the wall
  time of the parallel batch, while tokens and dollars sum over ALL K calls.
* **Semantic oracle** — every candidate is executed on the full test suite;
  candidates that raise or fail any test are discarded.
* **Selection** — among the surviving candidates, return the one with the
  smallest token-based edit distance to the student's submission.
* **Few-shot** (Sec. 4.2.2, Fig. 7) — the example bank pairs each pool buggy
  program p with its structurally nearest correct solution p' from the
  reference pool (the corpus has no per-student edit histories, so the correct
  side of each shot is drawn from the class's correct pool — the same pool
  every per-assignment system consumes). The three most similar p — by
  1 − normalized Hamming distance between test-failure vectors — are laid out
  as shots before the target program; the target itself is never its own shot.

Accounting: ALL K calls are summed into in/out tokens, $ and API seconds —
including candidates that fail the oracle — exactly as a real deployment pays.
There is no iterative refinement in the semantic phase.
"""
from __future__ import annotations

import io
import tokenize
from dataclasses import dataclass, field
from pathlib import Path

from src.runner._values import decode
from src.runner.testing import run_tests
from src.utils import llm as llm_mod

K_DEFAULT = 10
SHOTS = 3
PROMPT_TESTS_CAP = 4          # test cases shown in the prompt (oracle uses all)


# ------------------------------------------------------------------ prompts
def _tests_text(problem: dict, cap: int = PROMPT_TESTS_CAP) -> str:
    """Instructor test cases in the paper's '#input: / # output :' layout."""
    blocks = []
    for t in (problem.get("tests") or [])[:cap]:
        if "stdin" in t:
            tin, tout = t["stdin"].rstrip("\n"), str(t["expected"]).rstrip("\n")
        else:
            entry = t.get("entry", problem.get("entry"))
            tin = f"{entry}({', '.join(map(repr, decode(t.get('args', []))))})"
            tout = str(decode(t.get("expected")))
        blocks.append(f"#input:\n{tin}\n# output :\n{tout}")
    return "\n\n".join(blocks)


def _desc_text(problem: dict) -> str:
    return "\n".join("# " + l if l.strip() else "#"
                     for l in (problem.get("description", "").strip().splitlines() or [""]))


def zero_shot_prompt(buggy: str, problem: dict) -> str:
    """Fig. 6: buggy program, problem description, test suite, completion cue."""
    return (f"[[Buggy Program]]\n"
            f"### Buggy Program ###\n{buggy.rstrip()}\n\n\n"
            f"[[Problem Description]]\n{_desc_text(problem)}\n\n"
            f"[[Test Suite]]\n{_tests_text(problem)}\n\n"
            f"### Correct Program ###\n")


def few_shot_prompt(shots: list[tuple[str, str]], buggy: str,
                    problem: dict) -> str:
    """Fig. 7: shots as a prefix, target program, test suite, completion cue."""
    parts = []
    for p, p_fixed in shots:
        parts.append(f"[[Shot Starts]]\n# Incorrect Program #\n{p.rstrip()}\n"
                     f"# Correct Program #\n{p_fixed.rstrip()}\n[Shot Ends]")
    parts.append(f"[[Buggy Program Starts]]\n### Buggy Program ###\n"
                 f"{buggy.rstrip()}\n[[Buggy Program Ends]]")
    parts.append(f"[[Test Suite Starts]]\n{_tests_text(problem)}\n"
                 f"[[Test Suite Ends]]")
    parts.append("### Correct Program ###\n")
    return "\n\n".join(parts)


# ------------------------------------------------------------------ selection
def _tokens(source: str) -> list[str]:
    try:
        return [t.string for t in
                tokenize.generate_tokens(io.StringIO(source).readline)
                if t.string.strip()]
    except (tokenize.TokenizeError, IndentationError, SyntaxError):
        return source.split()


def token_edit_distance(a: str, b: str) -> int:
    """Levenshtein distance over lexical tokens (Yasunaga & Liang 2021)."""
    ta, tb = _tokens(a), _tokens(b)
    if len(ta) > len(tb):
        ta, tb = tb, ta
    prev = list(range(len(ta) + 1))
    for j, y in enumerate(tb, 1):
        cur = [j]
        for i, x in enumerate(ta, 1):
            cur.append(min(prev[i] + 1, cur[i - 1] + 1,
                           prev[i - 1] + (x != y)))
        prev = cur
    return prev[-1]


# ------------------------------------------------------------------ few-shot bank
class ShotBank:
    """(p, p') example bank with failure-vector retrieval (Sec. 4.2.2).

    Bank construction: every pool buggy program p is paired with its
    structurally nearest correct solution p' from the reference pool (TF-IDF
    over normalized-AST paths, cosine). Failure vectors are computed once per
    bank program on the full suite; ``bank_cap`` bounds that one-time cost on
    very large pools.
    """

    def __init__(self, problem: dict, data_dir: Path, bank_cap: int = 150):
        self.problem = problem
        self.entries: list[tuple[tuple, str, str]] = []
        buggy_files = sorted((data_dir / "buggy").glob("*.py"))[:bank_cap]
        correct = [f.read_text()
                   for f in sorted((data_dir / "correct").glob("*.py"))]
        if not buggy_files or not correct:
            return
        from sklearn.metrics import pairwise_distances

        from src.core.cluster import structural_features
        buggy_srcs = [f.read_text() for f in buggy_files]
        matrix, vec = structural_features(buggy_srcs + correct)
        if vec is None:
            return
        X = matrix.toarray() if hasattr(matrix, "toarray") else matrix
        B, C = X[:len(buggy_srcs)], X[len(buggy_srcs):]
        nearest = pairwise_distances(B, C, metric="cosine").argmin(axis=1)
        for i, p_src in enumerate(buggy_srcs):
            self.entries.append((self._vector(p_src), p_src,
                                 correct[int(nearest[i])]))

    def _vector(self, source: str) -> tuple:
        res = run_tests(source, self.problem)
        return res.signature()

    def retrieve(self, buggy: str, k: int = SHOTS) -> list[tuple[str, str]]:
        """Top-k most similar bank entries; the target is never its own shot."""
        pool = [e for e in self.entries if e[1] != buggy]
        if not pool:
            return []
        tv = self._vector(buggy)

        def sim(vec):
            n = max(len(vec), len(tv), 1)
            ham = sum(1 for a, b in zip(vec, tv) if (a == "pass") != (b == "pass"))
            ham += abs(len(vec) - len(tv))
            return 1 - ham / n

        ranked = sorted(pool, key=lambda e: -sim(e[0]))
        return [(p, pf) for _v, p, pf in ranked[:k]]


# ------------------------------------------------------------------ repair
@dataclass
class PyDexResult:
    repaired: bool
    patch: str | None
    calls: int = 0
    valid: int = 0                 # candidates that passed the full suite
    in_tokens: int = 0
    out_tokens: int = 0
    seconds: float = 0.0           # summed API latency across ALL calls
    usd: float = 0.0
    prompt: str = ""               # the prompt used (for prefix analysis)
    # every sampled candidate with its own accounting, in call order, so a
    # different oracle or a smaller K can be judged later without re-querying
    candidates: list[dict] = field(default_factory=list)


def repair(buggy: str, problem: dict, model: str = "claude-sonnet-5",
           k: int = K_DEFAULT, bank: ShotBank | None = None,
           llm_fn=None) -> PyDexResult:
    """One semantic-phase repair: K sampled candidates, oracle, min-edit pick."""
    shots = bank.retrieve(buggy) if bank is not None else []
    prompt = (few_shot_prompt(shots, buggy, problem) if shots
              else zero_shot_prompt(buggy, problem))
    call = llm_fn or llm_mod.complete

    res = PyDexResult(False, None, prompt=prompt)
    survivors: list[str] = []
    import time as _time
    from concurrent.futures import ThreadPoolExecutor
    t0 = _time.time()
    with ThreadPoolExecutor(max_workers=k) as ex:
        comps = list(ex.map(lambda _:
                            call(prompt, model=model, temperature=None), range(k)))
    res.seconds = _time.time() - t0            # parallel-batch wall (one round trip)
    for comp in comps:
        res.calls += 1
        res.in_tokens += comp.in_tokens
        res.out_tokens += comp.out_tokens
        res.usd += comp.usd
        code = comp.code
        res.candidates.append({"code": code, "in": comp.in_tokens,
                               "out": comp.out_tokens, "usd": comp.usd})
        if not code:
            continue
        if run_tests(code, problem).all_pass:
            survivors.append(code)

    res.valid = len(survivors)
    if survivors:
        res.repaired = True
        res.patch = min(survivors, key=lambda c: token_edit_distance(buggy, c))
    return res
