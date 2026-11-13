def gen(rng):
    n = rng.randint(0, 10)
    lst = [rng.randint(-3, 7) for _ in range(n)]
    if n == 0:
        k = 0
    else:
        choices = [0, 1, n]
        if n > 1:
            choices.extend([rng.randint(0, n)])
        k = rng.choice(choices)
        if rng.random() < 0.2:
            k = rng.randint(0, n)
    return {"args": [lst, k]}