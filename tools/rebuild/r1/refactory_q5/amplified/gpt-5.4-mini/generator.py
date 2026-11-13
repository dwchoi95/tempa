def gen(rng):
    n = rng.randint(0, 10)
    lst = [rng.randint(-3, 9) for _ in range(n)]
    k = rng.randint(0, n)
    return {"args": [lst, k]}