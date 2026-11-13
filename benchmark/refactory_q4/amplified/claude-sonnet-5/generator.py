def gen(rng):
    n = rng.choice([0, 1] + list(range(2, 11)))
    ages = rng.sample(range(1, 100), n)
    genders = ["M", "F"]
    people = [[rng.choice(genders), age] for age in ages]
    return {"args": [people]}