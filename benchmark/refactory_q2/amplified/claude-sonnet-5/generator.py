import random

def gen(rng):
    months_pool = ["January", "February", "March", "April", "May"]
    days_pool = [str(i) for i in range(1, 6)]

    entry = rng.choice(["unique_day", "unique_month", "contains_unique_day"])

    length = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 8, 10])
    birthdays = []
    for _ in range(length):
        m = rng.choice(months_pool)
        d = rng.choice(days_pool)
        birthdays.append([m, d])

    if entry == "unique_day":
        if birthdays and rng.random() < 0.7:
            query = rng.choice(birthdays)[1]
        else:
            query = rng.choice(days_pool)
        args = [query, birthdays]
    elif entry == "unique_month":
        if birthdays and rng.random() < 0.7:
            query = rng.choice(birthdays)[0]
        else:
            query = rng.choice(months_pool)
        args = [query, birthdays]
    else:
        if birthdays and rng.random() < 0.7:
            query = rng.choice(birthdays)[0]
        else:
            query = rng.choice(months_pool)
        args = [query, birthdays]

    return {"args": args, "entry": entry}