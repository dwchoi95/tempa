def gen(rng):
    funcs = ["unique_day", "unique_month", "contains_unique_day", None]
    entry = rng.choice(funcs)

    months = ["January", "February", "March", "April"]
    days = ["1", "2", "3", "10"]

    n = rng.randint(0, 6)
    possible_birthdays = []
    for _ in range(n):
        possible_birthdays.append([rng.choice(months), rng.choice(days)])

    if entry == "unique_day":
        day = rng.choice(days)
        return {"args": [day, possible_birthdays], "entry": "unique_day"}
    elif entry == "unique_month":
        month = rng.choice(months)
        return {"args": [month, possible_birthdays], "entry": "unique_month"}
    elif entry == "contains_unique_day":
        month = rng.choice(months)
        return {"args": [month, possible_birthdays], "entry": "contains_unique_day"}
    else:
        month = rng.choice(months)
        return {"args": [month, possible_birthdays]}