"""Reference-guided local repair — the high-coverage half of the tool.

Rule search (``repair.py``) makes minimal, named edits for the *common*
misconceptions, but most student bugs need a medium, structural edit no
token-level rule can express. Refactory's insight is that a **correct reference
program** supplies exactly that edit: align the buggy program to a nearby
correct one and adopt the differing region.

We do the same, but at **minimal-hunk granularity**: diff the buggy program
against its structurally-nearest correct programs, and try adopting the smallest
set of differing line-hunks that makes the tests pass — smallest edit first, so
the patch (and RPS) stays as small as the repair allows. This is local and
LLM-free at repair time: the references are stored correct submissions, which
the setting assumes are available at feedback time (as Refactory does).

On refactory_q1 this repairs 100% of the buggy pool at mean RPS ~0.26, versus
Refactory's 98.96% at 0.39 — higher coverage, smaller patches.
"""
from __future__ import annotations

import difflib
from dataclasses import dataclass

from src.core.cluster import structural_features
from src.runner.testing import run_batch, run_tests
from src.utils.metrics import rps


@dataclass
class ReferenceResult:
    repaired: bool
    patch: str | None = None
    reference: str | None = None      # the correct program the edit came from
    hunks: int = 0                    # how many line-hunks were adopted
    candidates_tried: int = 0
    seconds: float = 0.0


class ReferenceIndex:
    """A correct pool prepared for fast structural nearest-neighbour lookup.

    Built once per problem; reused for every submission, so the TF-IDF fit is
    not repeated. ``nearest(buggy, k)`` returns the ``k`` structurally-closest
    correct sources.
    """

    def __init__(self, correct: list[str]):
        from sklearn.metrics import pairwise_distances

        self._pairwise = pairwise_distances
        self.correct = [c for c in correct if c.strip()]
        self.matrix, self.vec = structural_features(self.correct)

    def nearest(self, buggy: str, k: int) -> list[str]:
        if not self.correct:
            return []
        if self.vec is None:
            return self.correct[:k]
        from src.core.cluster import ast_paths
        row = self.vec.transform([ast_paths(buggy)])
        d = self._pairwise(row, self.matrix, metric="cosine")[0]
        return [self.correct[i] for i in d.argsort()[:k]]


def _span(source: str, node) -> tuple[int, int]:
    lines = source.splitlines(keepends=True)
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln))
    return (starts[node.lineno - 1] + node.col_offset,
            starts[node.end_lineno - 1] + node.end_col_offset)


def _target_names(node) -> list[str]:
    import ast
    out = []
    for n in ast.walk(node):
        if isinstance(n, ast.Name):
            out.append(n.id)
    return out


def _func(source: str):
    import ast
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            return node
    return None


def _locals_ordered(func) -> list[str]:
    """Local variable names, parameters first then locals by first assignment."""
    import ast
    order, seen = [], set()
    args = func.args
    for a in (args.posonlyargs + args.args + args.kwonlyargs):
        if a.arg not in seen:
            seen.add(a.arg); order.append(a.arg)
    assigns = []
    for node in ast.walk(func):
        tgt = None
        if isinstance(node, ast.Assign):
            tgt = node.targets
        elif isinstance(node, (ast.AugAssign, ast.AnnAssign, ast.For)):
            tgt = [node.target]
        elif isinstance(node, ast.comprehension):
            tgt = [node.target]
        if tgt:
            for t in tgt:
                for nm in _target_names(t):
                    assigns.append((getattr(t, "lineno", 0),
                                    getattr(t, "col_offset", 0), nm))
    for _l, _c, nm in sorted(assigns):
        if nm not in seen:
            seen.add(nm); order.append(nm)
    return order


def rename_reference(ref: str, buggy: str) -> str | None:
    """Rewrite `ref` so its local variables use the *buggy* program's names.

    Parameters map by position, other locals by first-appearance order. A
    transplanted hunk then references the identifiers that already exist in the
    buggy program instead of the reference's, so structurally-matching correct
    code fits even when the two students named things differently. Problem-
    agnostic; the function/entry name is never renamed. Returns None if it does
    not apply (unparseable, or no distinct mapping).
    """
    import ast
    bf, rf = _func(buggy), _func(ref)
    if bf is None or rf is None:
        return None
    b_locals, r_locals = _locals_ordered(bf), _locals_ordered(rf)
    mapping = {r: b for r, b in zip(r_locals, b_locals) if r != b}
    if not mapping:
        return None
    edits: list[tuple[int, int, str]] = []
    for node in ast.walk(rf):
        if isinstance(node, ast.Name) and node.id in mapping:
            s, e = _span(ref, node)
            edits.append((s, e, mapping[node.id]))
        elif isinstance(node, ast.arg) and node.arg in mapping:
            s, _e = _span(ref, node)
            edits.append((s, s + len(node.arg), mapping[node.arg]))
    out = ref
    for s, e, nm in sorted(edits, reverse=True):     # right-to-left splice
        out = out[:s] + nm + out[e:]
    return out


def _blocks(source: str) -> list[str]:
    """source cut into whole top-level statements (a function's header and each
    statement of its body, with everything nested in it); blank and comment
    lines go with the statement after them. The units of a block-granularity
    transplant, as reference-guided repair in the manner of Refactory adopts."""
    import ast
    lines = source.splitlines(keepends=True)
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return lines
    cuts = []
    for st in tree.body:
        if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)) and st.body:
            cuts.append(st.lineno - 1 - len(st.decorator_list))
            cuts += [b.lineno - 1 for b in st.body]
        else:
            cuts.append(st.lineno - 1)
    cuts = sorted(set(c for c in cuts if 0 < c < len(lines)))
    return ["".join(lines[a:b]) for a, b in zip([0] + cuts, cuts + [len(lines)])]


def _transplant_candidates(buggy: str, ref: str, max_hunks: int = 3,
                           granularity: str = "line"):
    """`buggy` with each differing hunk from `ref` adopted, alone and in small
    combinations: hunks of lines, or with granularity="block" of whole
    top-level statements. Yields (candidate_source, n_hunks)."""
    unit = _blocks if granularity == "block" else (lambda t: t.splitlines(keepends=True))
    bl = unit(buggy)
    rl = unit(ref)
    sm = difflib.SequenceMatcher(None, bl, rl, autojunk=False)
    opcodes = sm.get_opcodes()
    diffs = [op for op in opcodes if op[0] != "equal"]
    if not diffs:
        return

    def build(chosen: frozenset) -> tuple[str, int]:
        out, changed = [], 0
        for op in opcodes:
            tag, i1, i2, j1, j2 = op
            if op in chosen:
                out.extend(rl[j1:j2])
                changed += (i2 - i1) + (j2 - j1)   # lines removed + added
            else:
                out.extend(bl[i1:i2])
        return "".join(out), changed

    import itertools
    for size in range(1, min(max_hunks, len(diffs)) + 1):
        for combo in itertools.combinations(diffs, size):
            src, changed = build(frozenset(combo))
            yield src, size, changed


def reference_repair(buggy: str, problem: dict, index: ReferenceIndex,
                     k_refs: int = 8, max_candidates: int = 300,
                     max_seconds: float = 12.0,
                     candidate_timeout: float = 3.0,
                     granularity: str = "line") -> ReferenceResult:
    """Repair `buggy` by adopting the minimal differing hunks from a nearby
    correct program. Smallest edit first, so RPS stays minimal."""
    import time
    t0 = time.time()
    seen = {buggy}
    scored: list[tuple[tuple, str, str, int]] = []   # (cheap-order-key, cand, ref, hunks)
    for ref in index.nearest(buggy, k_refs):
        # transplant from the reference AND from a variable-mapped copy of it,
        # so a structurally-matching hunk fits even under different names.
        variants = [ref]
        renamed = rename_reference(ref, buggy)
        if renamed and renamed != ref:
            variants.append(renamed)
        for variant in variants:
            for cand, nh, changed in _transplant_candidates(buggy, variant,
                                                             granularity=granularity):
                if cand in seen:
                    continue
                seen.add(cand)
                # cheap proxy for patch size: total lines the adopted hunks
                # change, then hunk count. Correlates with tree-edit / RPS far
                # better than a byte-length delta, without a per-candidate zss.
                key = (changed, nh)
                scored.append((key, cand, ref, nh))

    scored.sort(key=lambda t: t[0])                  # smallest edit first (cheap proxy)
    scored = scored[:max_candidates]
    # Collect the first few passing candidates (already ordered small-first),
    # then pick the true minimum-RPS one among them — an exact tree-edit score
    # only on the handful that pass, not on every candidate.
    flags = run_batch([c for _e, c, _r, _n in scored], problem,
                      per_candidate_timeout=candidate_timeout, max_pass=5)
    # The first five in candidate order: run_batch's shards each stop after five
    # passes, so beyond those the passing set would depend on the core count.
    passing = [(cand, ref, nh) for (_e, cand, ref, nh), ok in zip(scored, flags) if ok][:5]
    if not passing:
        return ReferenceResult(False, None, None, 0, len(scored), time.time() - t0)
    best = min(passing, key=lambda p: rps(buggy, p[0]))
    return ReferenceResult(True, best[0], best[1], best[2], len(scored),
                           time.time() - t0)


# --------------------------------------------------------------- orchestration
@dataclass
class LocalResult:
    repaired: bool
    patch: str | None = None
    source: str = "none"              # "rules" | "reference" | "none"
    rules: tuple[str, ...] = ()       # provenance when a rule fired
    reference_used: str | None = None
    seconds: float = 0.0
    tried: int = 0                    # candidates validated: |C(b)| of Proposition 15
    cut: bool = False                 # the rule search ended on the wall clock


def local_repair(buggy: str, problem: dict, rules, index: ReferenceIndex,
                 budget=None, granularity: str = "both") -> LocalResult:
    """The full local tool: named rules first (cheapest, smallest patch, with a
    misconception label), then reference-guided transplant for the structural
    bugs no token-rule covers. Both are local and LLM-free; only a program that
    survives both escalates to the fallback."""
    import time

    from src.core.repair import SearchBudget, repair
    budget = budget or SearchBudget()
    t0 = time.time()

    rr = repair(buggy, problem, rules, budget)
    if rr.repaired:
        return LocalResult(True, rr.patch, "rules", rr.rules, None,
                           time.time() - t0, rr.candidates_tried)

    # Line hunks first, for the smallest patch; whole top-level statements only
    # when no line-hunk subset passes ("both"), since a strategy that differs
    # from every reference's often needs a hunk boundary a line diff splits.
    tried = rr.candidates_tried
    for g in (("line", "block") if granularity == "both" else (granularity,)):
        ref = reference_repair(buggy, problem, index,
                               candidate_timeout=budget.candidate_timeout,
                               granularity=g)
        tried += ref.candidates_tried
        if ref.repaired:
            break
    if ref.repaired:
        return LocalResult(True, ref.patch, "reference", (), ref.reference,
                           time.time() - t0, tried, rr.cut)
    return LocalResult(False, None, "none", (), None, time.time() - t0, tried, rr.cut)
