import random

def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    weights=[10, 12, 10, 10, 9, 8, 7, 6, 5, 4, 3])[0]
    seq = sorted(rng.randint(-10, 10) for _ in range(n))
    if n == 0:
        x = rng.randint(-20, 20)
    else:
        mode = rng.randrange(6)
        if mode == 0:
            x = rng.choice(seq)
        elif mode == 1:
            x = seq[0] - rng.randint(1, 3)
        elif mode == 2:
            x = seq[-1] + rng.randint(1, 3)
        elif mode == 3:
            i = rng.randrange(n)
            x = seq[i] if rng.random() < 0.5 else seq[i] + rng.choice([0, 1, -1])
        elif mode == 4:
            x = rng.randint(-10, 10)
        else:
            x = rng.choice([seq[0], seq[-1], seq[0] - 1, seq[-1] + 1, rng.randint(-10, 10)])
    return {"args": [x, seq]}