def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], weights=[12, 12, 10, 10, 9, 8, 7, 6, 5, 4, 3])[0]
    vals = [rng.randint(0, 5) for _ in range(n)]
    return {"args": [vals]}