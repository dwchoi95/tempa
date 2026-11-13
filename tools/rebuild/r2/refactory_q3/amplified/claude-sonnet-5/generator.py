import random

def gen(rng):
    length = rng.choices(
        [0, 1, 2, 3, 5, 8, 10],
        weights=[2, 2, 2, 3, 3, 2, 1]
    )[0]
    value_pool_type = rng.choice(["small_int", "small_int_neg", "chars", "mixed"])
    if value_pool_type == "small_int":
        pool = list(range(0, rng.choice([2, 3, 4, 5])))
    elif value_pool_type == "small_int_neg":
        pool = list(range(-3, 4))
    elif value_pool_type == "chars":
        pool = list("abc")
    else:
        pool = [0, 1, "x", "y", True, None]

    lst = [rng.choice(pool) for _ in range(length)]

    if length > 0 and rng.random() < 0.2:
        idx = rng.randrange(length)
        lst[idx] = pool[0]

    return {"args": [lst]}