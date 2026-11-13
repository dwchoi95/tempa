def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], weights=[10, 12, 12, 12, 10, 10, 8, 6, 5, 3, 2])[0]
    ages = rng.sample(list(range(0, 31)), k=n) if n <= 31 else [rng.randrange(0, 31) for _ in range(n)]
    people = [[rng.choice(["M", "F"]), age] for age in ages]
    rng.shuffle(people)
    return {"args": [people]}