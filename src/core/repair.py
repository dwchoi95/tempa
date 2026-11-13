"""Rule-combination search driver, with rule provenance.

A generated tool (``tools/<p_id>/<model>/fixer.rules``) compiles to rules that
are *candidate generators*: each rule maps a source string to zero or more
edited source strings. This driver composes them, validates every candidate
against the problem's tests, and stops as soon as one passes.

Two properties the rest of the system depends on:

* **Termination is test-pass only.** There is no patch-size gate; RPS is
  measured afterwards and reported, never used to reject a repair.
* **Provenance is recorded.** Every emitted patch carries the ordered list of
  rule identifiers that produced it, so per-rule statistics (which
  misconception fired how often) are available without re-running anything.
  v1 discarded this information; recovering it was impossible after the fact.

Search order is failure-signature driven: rules whose declared symptoms match
the program's failing tests are tried first, then single rules, then pairs,
then longer combinations, under an explicit budget rather than a blind 2^|R|.

Only the instructor's tests T shape the search: the signature that orders the
rules, and the time limits that stop a candidate from being rewritten further,
are taken on T, and the amplified tests only decide which candidate is
accepted. The candidates a search can return are then fixed before T_amp is
drawn, which the union bound of Proposition 15 needs.
"""
from __future__ import annotations

import ast
import signal
import threading
import time
from dataclasses import dataclass, field

from src.runner.testing import run_batch, run_tests

# A generated rule can contain an infinite loop; a rule's apply() runs in this
# process, so no subprocess timeout bounds it. Cap it with a wall-clock alarm.
RULE_APPLY_TIMEOUT = 2.0


def edit_sites(a, b) -> int:
    """Maximal AST positions at which ``a`` and ``b`` differ.

    A position is a node whose own name, constant or operator changed, a node
    replaced by one of another type, or one run of a statement or expression
    list replaced by another (an insertion or deletion is such a run).
    """
    if type(a) is not type(b):
        return 1
    if isinstance(a, list):
        if len(a) == len(b):
            return sum(edit_sites(x, y) for x, y in zip(a, b))
        return 1
    if isinstance(a, ast.AST):
        n = 0
        for f in a._fields:
            x, y = getattr(a, f, None), getattr(b, f, None)
            if isinstance(x, (ast.AST, list)) or isinstance(y, (ast.AST, list)):
                n += edit_sites(x, y) if (x is not None and y is not None) else 1
            elif x != y:
                return 1
        return n
    return 0 if a == b else 1


def single_site(source: str, candidate: str, _tree: ast.AST | None = None) -> bool:
    """The rule contract: one application rewrites exactly one AST position,
    a subtree or a run of a list, and leaves the rest of the program alone."""
    try:
        return edit_sites(_tree or ast.parse(source), ast.parse(candidate)) == 1
    except (SyntaxError, MemoryError, RecursionError):
        # Unparsable, or nested past the parser's or the interpreter's stack
        # (a rule re-applied down a long chain of one-candidate layers): no
        # program the tests could run.
        return False


class _RuleTimeout(BaseException):
    """Not an ``Exception`` on purpose: a generated rule's ``except Exception``
    must not swallow its own runaway-loop timeout."""


def _apply_bounded(fn, source, seconds):
    """Run ``fn(source)`` under a wall-clock alarm (main thread + POSIX only)."""
    can_alarm = (hasattr(signal, "setitimer")
                 and threading.current_thread() is threading.main_thread())
    if not can_alarm:
        return fn(source)
    old = signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(_RuleTimeout()))
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        return fn(source)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


@dataclass
class RepairResult:
    """Outcome of repairing one buggy program."""
    repaired: bool
    patch: str | None = None
    rules: tuple[str, ...] = ()          # provenance: rules that produced the patch
    candidates_tried: int = 0
    seconds: float = 0.0
    source: str = "local"                # "local" | "fallback" | "none"
    failure_signature: tuple[str, ...] = ()
    cut: bool = False                    # the node budget ended the search, not exhaustion
    pruned: int = 0                      # candidates skipped unvalidated by their footprint

    def as_dict(self) -> dict:
        return {"repaired": self.repaired, "rules": list(self.rules),
                "candidates_tried": self.candidates_tried,
                "seconds": round(self.seconds, 3), "source": self.source,
                "failure_signature": list(self.failure_signature)}


@dataclass
class Rule:
    """One named repair rule from a generated tool.

    ``symptoms`` lets a rule declare which failure classes it targets
    (e.g. ``("wrong",)`` or ``("err:TypeError",)``); it is used only for search
    ordering, never for correctness.
    """
    name: str
    apply: callable                       # (source) -> Iterable[str]
    symptoms: tuple[str, ...] = ()
    local: bool = False                   # single-site by construction (src/core/rulelang.py)
    total: bool = False                   # always terminates (src/core/rulelang.py): no alarm
    neutral: bool = False                 # scope-neutral (src/core/rulelang.py): footprint = sites

    def __call__(self, source: str):
        try:
            out = (self.apply(source) if self.total
                   else _apply_bounded(self.apply, source, RULE_APPLY_TIMEOUT))
        except (Exception, _RuleTimeout):     # bad rule (crash or runaway loop)
            return []
        if out is None:
            return []
        out = [out] if isinstance(out, str) else list(out)
        if self.local:                        # the rule language guarantees it
            return [c for c in out if isinstance(c, str)]
        # Enforce the contract the builder is asked to follow: a candidate that
        # rewrites more than one position is not this rule's to propose.
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return out                         # nothing to compare against
        return [c for c in out if isinstance(c, str) and single_site(source, c, tree)]


@dataclass
class SearchBudget:
    candidate_timeout: float = 3.0        # hard wall per candidate (subprocess kill)
    max_nodes: int = 1000                 # eta_search: candidates the rule search validates
    prune: bool = False                   # skip candidates by footprint (by Theorem 5)


def _ordered(rules: list[Rule], signature: tuple[str, ...]) -> list[Rule]:
    """Rules whose declared symptoms occur in this program's failures first."""
    present = set(signature)
    return sorted(rules, key=lambda r: 0 if (set(r.symptoms) & present) else 1)


def instructor(problem: dict) -> dict:
    """The problem restricted to T, the first ``n_instructor`` of its tests."""
    n = problem.get("n_instructor")
    return problem if n is None or n >= len(problem["tests"]) else dict(
        problem, tests=problem["tests"][:n])


def repair(source: str, problem: dict, rules: list[Rule],
           budget: SearchBudget | None = None) -> RepairResult:
    """Search rule combinations until all tests pass or the budget is spent."""
    budget = budget or SearchBudget()
    t0 = time.time()

    # No shortcut for a submission that already passes: the corpus labels it
    # buggy, so it enters the search like every other one and is measured on
    # whatever the strategies do to it. Returning it unedited would hand this
    # arm a free patch of size zero that the per-submission baselines, which
    # query the model regardless, never get.
    t_only = instructor(problem)
    base = run_tests(source, t_only, timeout=budget.candidate_timeout)
    signature = base.signature()
    ordered = _ordered(rules, signature)

    # Footprint pruning (by Theorem 5): a candidate whose footprint some failing
    # test of T never reaches has the buggy program's outcome on that test, so it
    # is no repair and is not validated; it still seeds the next layer. A test the
    # buggy program times out on traces only a prefix of its run, so it prunes
    # nothing. Unvalidated candidates do not count against the budget, so their
    # number is bounded apart, at ten times it.
    reach: list[set[int]] = []
    if budget.prune:
        for f in base.failures:
            if f.get("timeout"):
                continue
            one = run_tests(source, dict(t_only, tests=[t_only["tests"][f["index"]]]),
                            timeout=budget.candidate_timeout, trace=True)
            if one.error is None and one.total == 1 and one.passed == 0 and not any(
                    x.get("timeout") for x in one.failures):
                reach.append(set(one.lines))
    cap = 10 * budget.max_nodes
    neutral = {r.name: r.neutral for r in rules}

    # One depth at a time: expand every program found so far by one more rule
    # application, test that layer, and stop at the first layer that passes.
    #
    # Only the number of candidates validated is capped, not combination length
    # or fan-out: a submission repaired by one edit costs one small layer, and
    # the combinatorial blow-up two or three layers down is only ever reached by
    # submissions no rule set was going to repair anyway. A count rather than a
    # wall clock makes the search, and so every patch, independent of machine
    # load, and bounds |C(b)| in Proposition 15.
    #
    # Testing per layer also makes the shallowest repair the one returned, by
    # construction rather than by luck of ordering. Depth is a proxy for patch
    # size, and small patches are the point.
    frontier: list[tuple[str, tuple[str, ...]]] = [(source, ())]
    seen = {source}
    tried = pruned = 0
    exhausted = False

    while frontier and tried < budget.max_nodes and tried + pruned < cap:
        room = budget.max_nodes - tried
        layer: list[tuple[str, tuple[str, ...], bool]] = []    # (candidate, rules, pruned)
        n_val = 0

        def full() -> bool:
            return n_val >= room or tried + pruned + len(layer) >= cap
        for parent, prov in frontier:
            for rule in ordered:
                if full():
                    break
                for cand in rule(parent):
                    if cand in seen or full():
                        continue
                    seen.add(cand)
                    skip = bool(reach) and _misses(source, cand, reach,
                                                   all(neutral[n] for n in prov + (rule.name,)))
                    layer.append((cand, prov + (rule.name,), skip))
                    n_val += not skip
            if full():
                break
        if not layer:
            exhausted = True
            break
        check = [(c, p) for c, p, s in layer if not s]
        tried += len(check)
        pruned += len(layer) - len(check)
        cands = [c for c, _ in check]
        if not cands:
            frontier = [(c, p) for c, p, _ in layer]
            continue
        # T first, every candidate: what passes it goes on to T+, and what ran
        # past a time limit on it is pruned, so T_amp never shapes the search.
        flags, hung = run_batch(cands, t_only, hangs=True, max_pass=len(cands),
                                per_candidate_timeout=budget.candidate_timeout)
        if t_only is not problem:
            on_t = [i for i, ok in enumerate(flags) if ok]
            full = run_batch([cands[i] for i in on_t], problem,
                             per_candidate_timeout=budget.candidate_timeout)
            flags = [False] * len(cands)
            for i, ok in zip(on_t, full):
                flags[i] = ok
        for (cand, prov), ok in zip(check, flags):
            if ok:
                return RepairResult(True, cand, prov, tried,
                                    time.time() - t0, "local", signature, pruned=pruned)
        # A candidate that ran past a time limit is not rewritten further: its
        # rewrites keep the loop that hangs it unless one fixes that loop, and a
        # rewrite at another site commutes with that fix, which the search then
        # reaches from a program that terminates.
        hangs = dict(zip(cands, hung))
        frontier = [(c, p) for c, p, s in layer if s or not hangs[c]]

    return RepairResult(False, None, (), tried, time.time() - t0,
                        "none", signature, cut=not exhausted, pruned=pruned)


def _misses(source: str, cand: str, reach: list[set[int]], neutral: bool) -> bool:
    """Whether some failing test, by the lines of ``source`` it executes, never
    reaches the footprint of ``source`` -> ``cand``. A candidate made by
    scope-neutral rules alone has its edited sites as its footprint (the effect
    theorem), so no scope of ``cand`` is analyzed."""
    from src.core.footprint import footprint_lines
    try:
        f = footprint_lines(source, cand, sites_only=neutral)
    except SyntaxError:
        return False
    return f is not None and any(not (r & f) for r in reach)


# --------------------------------------------------------------- provenance
@dataclass
class ProvenanceLog:
    """Per-rule firing statistics across a problem's evaluation set.

    This is what turns the generated tool into a *diagnosis of the class*:
    how often each misconception rule fired, and on which programs.
    """
    fired: dict[str, list[str]] = field(default_factory=dict)

    def record(self, program_id: str, result: RepairResult) -> None:
        for name in result.rules:
            self.fired.setdefault(name, []).append(program_id)

    def profile(self) -> list[tuple[str, int]]:
        """Rules ranked by how many programs they repaired."""
        return sorted(((k, len(v)) for k, v in self.fired.items()),
                      key=lambda kv: -kv[1])

    def as_dict(self) -> dict:
        return {"profile": [{"rule": k, "count": n} for k, n in self.profile()],
                "fired": self.fired}
