"""Paired significance tests over per-submission event logs.

The comparisons the paper makes are paired: the same submission is attempted by
every arm, so a two-sample proportion test would throw away the pairing and
overstate the uncertainty. McNemar's test uses only the discordant pairs -- the
submissions one arm repairs and the other does not -- which is exactly the
evidence that distinguishes them.

The exact binomial form is used rather than the chi-square approximation: the
discordant counts here are often small (four of the five CS1 assignments have
single-digit disagreements), where the approximation is unreliable.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import comb


@dataclass
class McNemar:
    n_pairs: int
    b: int          # a repairs, b does not
    c: int          # b repairs, a does not
    p_value: float

    @property
    def discordant(self) -> int:
        return self.b + self.c

    def __str__(self) -> str:
        return (f"n={self.n_pairs} b={self.b} c={self.c} "
                f"(discordant {self.discordant}) p={self.p_value:.4g}")


def mcnemar(a_fixed: dict[str, bool], b_fixed: dict[str, bool]) -> McNemar:
    """Exact two-sided McNemar test over submissions present in both arms.

    ``a_fixed``/``b_fixed`` map submission id to whether that arm repaired it.
    Only ids present in both are used, so an arm evaluated on a subset compares
    on the overlap rather than silently against a different denominator.
    """
    shared = a_fixed.keys() & b_fixed.keys()
    b = sum(1 for k in shared if a_fixed[k] and not b_fixed[k])
    c = sum(1 for k in shared if b_fixed[k] and not a_fixed[k])
    return McNemar(len(shared), b, c, _exact_p(b, c))


def _exact_p(b: int, c: int) -> float:
    """Two-sided exact binomial p on the discordant pairs (H0: p = 1/2)."""
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    tail = sum(comb(n, i) for i in range(k + 1)) / 2 ** n
    return min(1.0, 2 * tail)


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson score interval for a binomial proportion (default 95%).

    Preferred over the normal approximation because repair rates here sit near
    1.0, where the normal interval runs past it and can even exclude the
    observed value.
    """
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / d
    half = z * ((p * (1 - p) / n + z * z / (4 * n * n)) ** 0.5) / d
    return (max(0.0, centre - half), min(1.0, centre + half))
