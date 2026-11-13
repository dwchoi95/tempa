def gen(rng):
    n = rng.randint(0, 10)
    lst = [rng.randint(-3, 5) for _ in range(n)]
    if n == 0:
        k = 0
    else:
        choice = rng.random()
        if choice < 0.2:
            k = 0
        elif choice < 0.35:
            k = 1
        elif choice < 0.5:
            k = n
        else:
            k = rng.randint(0, n)
    return {"args": [lst, k]}