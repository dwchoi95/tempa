def gen(rng):
    n = rng.choice([0, 0, 1, 1] + list(range(2, 11)))
    values = range(-3, 4)
    lst = [rng.choice(list(values)) for _ in range(n)]
    return {"args": [lst]}