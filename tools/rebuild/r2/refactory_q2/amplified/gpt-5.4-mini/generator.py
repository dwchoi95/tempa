import random

def gen(rng):
    funcs = ["unique_day", "unique_month", "contains_unique_day"]
    entry = rng.choice(funcs + [None, None])  # sometimes omit entry, as in suite
    months = ["January", "February", "March"]
    days = ["1", "2", "3", "10"]
    n = rng.randint(0, 6)
    birthdays = []
    for _ in range(n):
        birthdays.append([rng.choice(months), rng.choice(days)])

    if entry == "unique_day":
        day = rng.choice(days)
        return {"args": [day, birthdays], "entry": entry}
    elif entry == "unique_month":
        month = rng.choice(months)
        return {"args": [month, birthdays], "entry": entry}
    elif entry == "contains_unique_day":
        month = rng.choice(months)
        return {"args": [month, birthdays], "entry": entry}
    else:
        month = rng.choice(months)
        return {"args": [month, birthdays]}