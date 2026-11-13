import random

def gen(rng):
    n = rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    pool = [-2, -1, 0, 1, 2, 3]
    lst = [rng.choice(pool) for _ in range(n)]
    return {"args": [lst]}