import random

def gen(rng):
    months = ["January", "February", "March", "April", "May"]
    days = [str(i) for i in range(1, 6)]

    entry = rng.choice(["unique_day", "unique_month", "contains_unique_day"])

    size = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 7, 8])
    birthdays = []
    for _ in range(size):
        m = rng.choice(months)
        d = rng.choice(days)
        birthdays.append([m, d])

    if entry == "unique_day":
        if rng.random() < 0.7 and birthdays:
            day = rng.choice(birthdays)[1]
        else:
            day = rng.choice(days)
        args = [day, birthdays]
        return {"args": args, "entry": "unique_day"}

    elif entry == "unique_month":
        if rng.random() < 0.7 and birthdays:
            month = rng.choice(birthdays)[0]
        else:
            month = rng.choice(months)
        args = [month, birthdays]
        return {"args": args, "entry": "unique_month"}

    else:
        if rng.random() < 0.7 and birthdays:
            month = rng.choice(birthdays)[0]
        else:
            month = rng.choice(months)
        args = [month, birthdays]
        return {"args": args}