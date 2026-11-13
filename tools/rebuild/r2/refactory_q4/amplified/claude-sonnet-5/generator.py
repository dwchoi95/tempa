def gen(rng):
    n = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    ages = rng.sample(range(1, 100), n)
    genders = ["M", "F"]
    people = [[rng.choice(genders), age] for age in ages]
    return {"args": [people]}