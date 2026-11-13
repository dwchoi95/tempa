import random

def gen(rng):
    n = rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    low, high = -10, 10
    vals = sorted(rng.randint(low, high) for _ in range(n))
    if rng.random() < 0.3 and vals:
        x = rng.choice(vals)
    elif rng.random() < 0.3:
        x = rng.choice([low - 1, high + 1, low, high])
    else:
        x = rng.randint(low - 2, high + 2)
    return {"args": [x, vals]}