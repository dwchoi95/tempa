def gen(rng):
    n = rng.randint(0, 10)
    lo, hi = rng.choice([(-5, 5), (0, 9), (1, 3), (-10, 10)])
    lst = [rng.randint(lo, hi) for _ in range(n)]
    k = rng.randint(0, n)
    return {"args": [lst, k]}