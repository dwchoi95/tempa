import random

def gen(rng):
    n = rng.randint(0, 10)
    low, high = -5, 5
    lst = [rng.randint(low, high) for _ in range(n)]
    k = rng.randint(0, n)
    return {"args": [lst, k]}