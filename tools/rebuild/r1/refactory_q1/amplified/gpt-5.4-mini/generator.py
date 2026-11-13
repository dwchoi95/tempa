import random

def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    weights=[12, 10, 10, 10, 10, 8, 8, 7, 7, 4, 4])[0]
    pool = [-5, -1, 0, 1, 3, 5, 7, 10, 42]
    seq = sorted(rng.choices(pool, k=n))
    if seq and rng.random() < 0.65:
        x = rng.choice(seq)
    else:
        x = rng.choice(pool)
        if rng.random() < 0.35 and seq:
            i = rng.randrange(len(seq) + 1)
            if i == 0:
                x = seq[0] - rng.choice([1, 2, 5, 10])
            elif i == len(seq):
                x = seq[-1] + rng.choice([1, 2, 5, 10])
            else:
                a, b = seq[i - 1], seq[i]
                if a < b:
                    x = rng.choice([a, b, (a + b) // 2])
    return {"args": [x, seq]}