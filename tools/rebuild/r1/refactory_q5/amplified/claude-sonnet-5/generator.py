import random

def gen(rng):
    n = rng.choice([0, 1, 1, 2, 3, 5, 7, 10])
    low, high = rng.choice([(-3, 3), (0, 1), (1, 9), (-5, 5), (0, 0)])
    lst = [rng.randint(low, high) for _ in range(n)]
    k = rng.randint(0, n)
    return {"args": [lst, k]}