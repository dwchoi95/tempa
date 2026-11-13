def gen(rng):
    n = rng.choice([0, 1, 2, 3, rng.randint(0, 10)])
    n = max(0, min(n, 10))
    ages = rng.sample(range(1, 100), n)
    people = []
    for age in ages:
        gender = rng.choice(["M", "F"])
        people.append([gender, age])
    rng.shuffle(people)
    return {"args": [people]}