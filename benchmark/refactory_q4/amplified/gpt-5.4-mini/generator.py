def gen(rng):
    n = rng.choices([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], weights=[8, 10, 10, 10, 10, 10, 10, 8, 6, 4, 4])[0]
    ages_pool = list(range(0, 41))
    ages = rng.sample(ages_pool, n) if n <= len(ages_pool) else [rng.randrange(0, 41) for _ in range(n)]
    genders = ["M", "F"]
    people = [[rng.choice(genders), age] for age in ages]
    rng.shuffle(people)
    return {"args": [people]}