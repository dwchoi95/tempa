"""C1-C6 independent held-out inputs: one generator and one reference solution per
problem, written from the problem statement in benchmark/<pid>/problem.json only
(no builder generator, no submission was read to write them).

gen(pid, rng) -> (class, stdin)      ref(pid, stdin) -> expected stdout

    python3 gens.py     # self-check: every reference passes every official test,
                        # every generated input satisfies the stated constraints
"""
import math
import random
from collections import Counter

DIG_LUCKY, DIG_OTHER = "47", "01235689"


def _num(digits):                                  # no leading zero
    return digits.lstrip("0") or None


# ---------------------------------------------------------------- C1 110A
def _c1(rng):
    """1 <= n <= 10^18; YES iff the count of 4/7 digits is a lucky number."""
    cls = rng.choice(["random", "random", "count", "count", "all_lucky", "zeros", "edge"])
    if cls == "random":
        L = rng.randint(1, 18)
        s = rng.choice("123456789") + "".join(rng.choice("0123456789") for _ in range(L - 1))
    elif cls == "count":                           # exactly c lucky digits, c near 4 and 7
        c = rng.choice([0, 1, 2, 3, 4, 4, 4, 5, 6, 7, 7, 7, 8, 11, 14, 17])
        L = rng.randint(max(c, 1), 18)
        pos = set(rng.sample(range(L), c))
        s = "".join(rng.choice(DIG_LUCKY) if i in pos else rng.choice(DIG_OTHER) for i in range(L))
        if s[0] == "0":
            s = rng.choice("12356789") + s[1:]
    elif cls == "all_lucky":                       # a lucky number itself: YES iff its length is 4 or 7
        s = "".join(rng.choice(DIG_LUCKY) for _ in range(rng.randint(1, 18)))
    elif cls == "zeros":                           # lucky digits followed by zeros
        c = rng.choice([4, 7, 3, 5])
        s = "".join(rng.choice(DIG_LUCKY) for _ in range(c)) + "0" * rng.randint(1, 18 - c)
    else:
        s = rng.choice([str(10 ** 18), "9" * 18, "4" * 18, "7" * 18, "1", "4", "7", "44", "47",
                        "4" * 4 + "0" * 14, "7" * 7 + "0" * 11, str(10 ** 17), "4" * 7 + "9" * 11,
                        "4" * 17, "7" * 4 + "1" * 14, "1" + "4" * 4 + "0" * 13])
    return cls, s + "\n"


def _r1(stdin):
    c = sum(ch in "47" for ch in stdin.split()[0])
    return "YES" if c > 0 and set(str(c)) <= set("47") else "NO"


# ---------------------------------------------------------------- C2 131A
_LOW, _UP = "abcdefghijklmnopqrstuvwxyz", "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


def _c2(rng):
    """A word of 1..100 Latin letters; swap every letter's case iff all letters
    except possibly the first are uppercase."""
    cls = rng.choice(["mixed", "first_low_rest_up", "all_up", "all_low", "first_up_rest_low",
                      "one_low_inside", "single", "max_len"])
    L = rng.choice([rng.randint(2, 6), rng.randint(2, 100)])
    up = lambda k: "".join(rng.choice(_UP) for _ in range(k))
    low = lambda k: "".join(rng.choice(_LOW) for _ in range(k))
    if cls == "mixed":
        w = "".join(rng.choice(_LOW + _UP) for _ in range(L))
    elif cls == "first_low_rest_up":
        w = low(1) + up(L - 1)
    elif cls == "all_up":
        w = up(L)
    elif cls == "all_low":
        w = low(L)
    elif cls == "first_up_rest_low":
        w = up(1) + low(L - 1)
    elif cls == "one_low_inside":                  # rule fails at one letter after the first
        w = list(rng.choice([low, up])(1) + up(L - 1))
        i = rng.randint(1, L - 1)
        w[i] = w[i].lower()
        w = "".join(w)
    elif cls == "single":
        w = rng.choice(_LOW + _UP)
    else:
        w = rng.choice([low(1) + up(99), up(100), low(100), up(1) + low(99), up(99) + low(1),
                        "".join(rng.choice(_LOW + _UP) for _ in range(100))])
    return cls, w + "\n"


def _r2(stdin):
    w = stdin.split()[0]
    return w.swapcase() if w[1:] == w[1:].upper() else w


# ---------------------------------------------------------------- C3 1011B
def _c3(rng):
    """1 <= n, m <= 100, 1 <= a_i <= 100; max d with sum(cnt // d) >= n, else 0."""
    cls = rng.choice(["random", "few_types", "n_gt_m", "n_eq_m", "one_type", "distinct",
                      "n1", "m1", "max", "skewed"])
    n, m = rng.randint(1, 100), rng.randint(1, 100)
    if cls == "random":
        a = [rng.randint(1, 100) for _ in range(m)]
    elif cls == "few_types":
        ts = rng.sample(range(1, 101), rng.randint(2, 5))
        a = [rng.choice(ts) for _ in range(m)]
        n = rng.randint(1, max(1, m // 2))
    elif cls == "n_gt_m":
        m = rng.randint(1, 99)
        n = rng.randint(m + 1, 100)
        a = [rng.randint(1, 100) for _ in range(m)]
    elif cls == "n_eq_m":
        n = m
        a = [rng.randint(1, rng.choice([3, 100])) for _ in range(m)]
    elif cls == "one_type":
        a = [rng.randint(1, 100)] * m
        n = rng.randint(1, m)
    elif cls == "distinct":
        m = rng.randint(1, 100)
        a = rng.sample(range(1, 101), m)
        n = rng.randint(1, 100)
    elif cls == "n1":
        n = 1
        a = [rng.randint(1, rng.choice([5, 100])) for _ in range(m)]
    elif cls == "m1":
        m = 1
        a = [rng.randint(1, 100)]
        n = rng.randint(1, 3)
    elif cls == "max":
        n, m = rng.choice([(100, 100), (1, 100), (50, 100), (100, 99), (rng.randint(1, 100), 100)])
        a = [rng.randint(1, rng.choice([1, 2, 10, 100])) for _ in range(m)]
    else:                                          # one dominant type plus singletons
        k = rng.randint(1, m)
        a = [rng.randint(1, 100)] * k + [rng.randint(1, 100) for _ in range(m - k)]
        rng.shuffle(a)
        n = rng.randint(1, max(1, k // rng.randint(1, 4)))
    return cls, f"{n} {m}\n{' '.join(map(str, a))}\n"


def _r3(stdin):
    t = list(map(int, stdin.split()))
    n, m, a = t[0], t[1], t[2:]
    cnt = Counter(a).values()
    return str(max([d for d in range(1, 101) if sum(c // d for c in cnt) >= n], default=0))


# ---------------------------------------------------------------- C4 125A
def _c4(rng):
    """1 <= n <= 10000; inches = n/3 rounded with 1 cm -> 0 and 2 cm -> 1 inch."""
    cls = rng.choice(["random", "random", "foot_edge", "small", "large", "mod3"])
    if cls == "random":
        n = rng.randint(1, 10000)
    elif cls == "foot_edge":                       # around a whole number of feet (36 cm)
        n = 36 * rng.randint(1, 277) + rng.randint(-2, 2)
    elif cls == "small":
        n = rng.randint(1, 40)
    elif cls == "large":
        n = rng.randint(9960, 10000)
    else:
        n = 3 * rng.randint(0, 3332) + rng.choice([1, 2])
    return cls, f"{n}\n"


def _r4(stdin):
    inches = (int(stdin.split()[0]) + 1) // 3
    return f"{inches // 12} {inches % 12}"


# ---------------------------------------------------------------- C5 11B
def _tri(k):
    return k * (k + 1) // 2


def _c5(rng):
    """-10^9 <= x <= 10^9; fewest jumps 1, 2, ..., k with signs summing to x."""
    cls = rng.choice(["random", "small", "triangular", "triangular", "extreme"])
    sign = rng.choice([1, -1])
    if cls == "random":
        x = rng.randint(-10 ** 9, 10 ** 9)
    elif cls == "small":
        x = sign * rng.randint(0, 60)
    elif cls == "triangular":                      # T_k + d: the parity cases
        k = rng.choice([rng.randint(1, 30), rng.randint(1, 44720)])
        x = sign * max(0, min(10 ** 9, _tri(k) + rng.randint(-3, 3)))
    else:
        x = sign * rng.choice([10 ** 9, 10 ** 9 - 1, 10 ** 9 - 2, _tri(44720), _tri(44720) + 1,
                               _tri(44720) - 1, 10 ** 9 - 3, 10 ** 9 - 5])
    return cls, f"{x}\n"


def _r5(stdin):
    x = abs(int(stdin.split()[0]))
    k = math.isqrt(2 * x)
    while _tri(k) < x:
        k += 1
    while (_tri(k) - x) % 2:
        k += 1
    return str(k)


# ---------------------------------------------------------------- C6 10C
def _c6(rng):
    """1 <= N <= 10^6; triples with d(C) = d(d(A) d(B)) but AB != C."""
    cls = rng.choice(["small", "random", "loguniform", "mod9_edge", "square_edge", "large"])
    if cls == "small":
        n = rng.randint(1, 60)
    elif cls == "random":
        n = rng.randint(1, 10 ** 6)
    elif cls == "loguniform":
        n = int(10 ** rng.uniform(0, 6))
    elif cls == "mod9_edge":
        n = min(10 ** 6, max(1, 9 * rng.choice([rng.randint(1, 20), rng.randint(1, 111111)])
                             + rng.randint(-1, 1)))
    elif cls == "square_edge":                     # around perfect squares (sqrt-based counts)
        n = min(10 ** 6, max(1, rng.randint(1, 1000) ** 2 + rng.randint(-1, 1)))
    else:
        n = rng.randint(999000, 10 ** 6)
    return cls, f"{n}\n"


def _r6(stdin):
    n = int(stdin.split()[0])
    cnt = [n // 9 + (1 <= r <= n % 9) for r in range(9)]          # residues mod 9 in [1, n]
    billy = sum(cnt[i] * cnt[j] * cnt[i * j % 9] for i in range(9) for j in range(9))
    s = math.isqrt(n)
    true = 2 * sum(n // a for a in range(1, s + 1)) - s * s        # #{(A, B): AB <= n}
    return str(billy - true)


GEN = {"cf_110A": _c1, "cf_131A": _c2, "cf_1011B": _c3, "cf_125A": _c4, "cf_11B": _c5, "cf_10C": _c6}
REF = {"cf_110A": _r1, "cf_131A": _r2, "cf_1011B": _r3, "cf_125A": _r4, "cf_11B": _r5, "cf_10C": _r6}


def gen(pid, rng):
    return GEN[pid](rng)


def ref(pid, stdin):
    return REF[pid](stdin)


def valid(pid, stdin):
    """The statement's input constraints."""
    t = stdin.split()
    if pid == "cf_110A":
        return len(t) == 1 and t[0].isdigit() and t[0][0] != "0" and 1 <= int(t[0]) <= 10 ** 18
    if pid == "cf_131A":
        return len(t) == 1 and 1 <= len(t[0]) <= 100 and all(c in _LOW + _UP for c in t[0])
    if pid == "cf_1011B":
        n, m, a = int(t[0]), int(t[1]), list(map(int, t[2:]))
        return 1 <= n <= 100 and 1 <= m <= 100 and len(a) == m and all(1 <= v <= 100 for v in a)
    if pid == "cf_125A":
        return len(t) == 1 and 1 <= int(t[0]) <= 10000
    if pid == "cf_11B":
        return len(t) == 1 and -10 ** 9 <= int(t[0]) <= 10 ** 9
    if pid == "cf_10C":
        return len(t) == 1 and 1 <= int(t[0]) <= 10 ** 6
    raise ValueError(pid)


if __name__ == "__main__":
    import json
    from pathlib import Path
    B = Path(__file__).resolve().parents[3] / "benchmark"
    for pid in GEN:
        tests = json.loads((B / pid / "problem.json").read_text())["tests"]
        bad = [t["stdin"] for t in tests if ref(pid, t["stdin"]).split() != t["expected"].split()]
        assert not bad, (pid, bad[:3])
        rng = random.Random(0)
        draws = [gen(pid, rng) for _ in range(3000)]
        assert all(valid(pid, s) for _c, s in draws), pid
        print(f"{pid}: reference passes {len(tests)} official tests; 3000 draws valid; "
              f"{len({s for _c, s in draws})} distinct; classes {dict(Counter(c for c, _s in draws))}")
    # brute force for the two closed forms
    for x in range(-40, 41):                       # C5: BFS over reachable sums
        k, reach = 0, {0}
        while abs(x) not in reach and x not in reach:
            k += 1
            reach = {r + s for r in reach for s in (k, -k)}
        assert _r5(f"{x}\n") == str(k), x
    def droot(v):
        return 1 + (v - 1) % 9
    for n in range(1, 40):                         # C6: count triples directly
        brute = sum(1 for A in range(1, n + 1) for B_ in range(1, n + 1) for C in range(1, n + 1)
                    if droot(C) == droot(droot(A) * droot(B_)) and A * B_ != C)
        assert _r6(f"{n}\n") == str(brute), n
    print("brute-force checks of C5 (|x| <= 40) and C6 (N < 40) pass")
