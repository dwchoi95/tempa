import random

def gen(rng):
    funcs = ["unique_day", "unique_month", "contains_unique_day"]
    entry = rng.choice(funcs)

    months = ["January", "February", "March"]
    days = ["1", "2", "3", "10"]

    n = rng.randint(0, 6)
    possible_birthdays = [[rng.choice(months), rng.choice(days)] for _ in range(n)]

    if entry == "unique_day":
        day = rng.choice(days)
        return {"args": [day, possible_birthdays], "entry": entry}
    elif entry == "unique_month":
        month = rng.choice(months)
        return {"args": [month, possible_birthdays], "entry": entry}
    else:
        month = rng.choice(months)
        return {"args": [month, possible_birthdays], "entry": entry}