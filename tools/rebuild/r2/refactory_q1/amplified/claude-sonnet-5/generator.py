def gen(rng):
    n = rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    vals = []
    cur = rng.randint(-10, 0)
    for _ in range(n):
        cur += rng.randint(0, 3)
        vals.append(cur)
    if vals and rng.random() < 0.5:
        x = rng.choice(vals)
    else:
        x = rng.randint(min(vals, default=-10) - 5, max(vals, default=10) + 5)
    return {"args": [x, vals]}