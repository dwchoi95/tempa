import random

def gen(rng):
    n = rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 10])
    seq = []
    if n > 0:
        start = rng.randint(-10, 5)
        val = start
        for _ in range(n):
            step = rng.choice([0, 0, 1, 1, 2, 3])
            val += step
            seq.append(val)
    if seq and rng.random() < 0.5:
        x = rng.choice(seq)
    elif seq and rng.random() < 0.5:
        x = seq[0] - rng.randint(1, 5)
    elif seq and rng.random() < 0.5:
        x = seq[-1] + rng.randint(1, 5)
    else:
        x = rng.randint(-15, 15)
    return {"args": [x, seq]}