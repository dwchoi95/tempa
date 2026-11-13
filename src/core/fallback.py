"""LLM fallback with a strategy-matched reference.

When the local tool abstains, escalate to ``LLM(d, T, b, r)``: the prompt
carries a reference program ``r`` chosen to match the student's strategy
(``cluster.nearest_reference``), so the model sees a correct solution that most
likely tackles the problem the same way the student tried to.

The LLM call goes through ``src.utils.llm.complete`` so cost/latency accounting
is uniform; an ``llm_fn`` hook is accepted for tests, so this module is runnable
without an API key.
"""
from __future__ import annotations

from dataclasses import dataclass

from src.core.cluster import nearest_reference
from src.prompts import render
from src.runner._values import decode
from src.runner.testing import run_tests
from src.utils import llm as llm_mod


@dataclass
class FallbackResult:
    repaired: bool
    patch: str | None
    reference_used: str | None
    in_tokens: int = 0
    out_tokens: int = 0
    seconds: float = 0.0
    usd: float = 0.0
    candidate: str | None = None      # the model's code, kept even when it fails


def _render_failures(source: str, problem: dict, limit: int = 5) -> str:
    """Human-readable failing-test lines for the prompt."""
    res = run_tests(source, problem)
    lines = []
    for f in res.failures[:limit]:
        if f.get("timeout"):
            lines.append(f"- test {f['index']}: timed out")
        elif f.get("error"):
            lines.append(f"- test {f['index']}: {f['error']}")
        else:
            got = repr(decode(f.get("got")))[:120]
            exp = repr(decode(f.get("expected")))[:120]
            lines.append(f"- test {f['index']}: got {got}, expected {exp}")
    return "\n".join(lines) or "- (no per-test detail)"


def _render_tests(problem: dict, limit: int = 6) -> str:
    """A few example tests for the prompt, in whichever mode the problem uses."""
    lines = []
    for t in (problem.get("tests") or [])[:limit]:
        if "stdin" in t:
            lines.append(f"- input: {t['stdin']!r} -> output: {t['expected']!r}")
        else:
            entry = t.get("entry", problem.get("entry"))
            lines.append(f"- {entry}({', '.join(map(repr, decode(t.get('args', []))))}) "
                         f"= {decode(t.get('expected'))!r}")
    return "\n".join(lines)


def fallback_repair(buggy: str, problem: dict, reference_pool: list[str],
                    model: str = "claude-sonnet-5", llm_fn=None) -> FallbackResult:
    """Escalate one buggy program to the LLM with a strategy-matched reference.

    ``llm_fn(prompt, model)`` overrides the real API for testing; it must return
    an object with ``.code``, ``.in_tokens``, ``.out_tokens``, ``.seconds``,
    ``.usd`` (as :class:`src.utils.llm.Completion` does).
    """
    r = nearest_reference(buggy, reference_pool)
    prompt = render("fallback",
                    description=problem.get("description", ""),
                    tests=_render_tests(problem),
                    buggy=buggy,
                    failures=_render_failures(buggy, problem),
                    reference=r or "(no reference available)")
    call = (llm_fn or llm_mod.complete)(prompt, model=model)
    patch = call.code
    repaired = bool(patch) and run_tests(patch, problem, stop_early=True).all_pass
    return FallbackResult(
        repaired=repaired, patch=patch if repaired else None, reference_used=r,
        candidate=patch,
        in_tokens=call.in_tokens, out_tokens=call.out_tokens,
        seconds=call.seconds, usd=call.usd)

