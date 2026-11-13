def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    weights=[10, 12, 10, 10, 10, 10, 8, 7, 5, 4, 2])[0]
    vals = list(range(-2, 4))
    lst = []
    for _ in range(n):
        if lst and rng.random() < 0.55:
            lst.append(rng.choice(lst))
        else:
            lst.append(rng.choice(vals))
    if rng.random() < 0.15:
        lst = []
    elif rng.random() < 0.15:
        lst = [rng.choice(vals)]
    return {"args": [lst]}