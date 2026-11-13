def gen(rng):
    n = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    ages_pool = list(range(17, 25)) + [30, 35]
    ages = rng.sample(ages_pool, n) if n <= len(ages_pool) else [rng.choice(ages_pool) for _ in range(n)]
    genders = ["M", "F"]
    people = [[rng.choice(genders), age] for age in ages]
    rng.shuffle(people)
    return {"args": [people]}