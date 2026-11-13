import random

def gen(rng):
    months = ["January", "February", "March"]
    days = ["1", "2", "3", "10"]

    entry = rng.choice(["unique_day", "unique_month", "contains_unique_day"])

    n = rng.randint(0, 10)
    birthdays = []
    for _ in range(n):
        m = rng.choice(months)
        d = rng.choice(days)
        birthdays.append([m, d])

    if entry == "unique_day":
        if rng.random() < 0.5 and birthdays:
            day = rng.choice(birthdays)[1]
        else:
            day = rng.choice(days)
        return {"args": [day, birthdays], "entry": "unique_day"}

    elif entry == "unique_month":
        if rng.random() < 0.5 and birthdays:
            month = rng.choice(birthdays)[0]
        else:
            month = rng.choice(months)
        return {"args": [month, birthdays], "entry": "unique_month"}

    else:
        if rng.random() < 0.5 and birthdays:
            month = rng.choice(birthdays)[0]
        else:
            month = rng.choice(months)
        return {"args": [month, birthdays], "entry": "contains_unique_day"}