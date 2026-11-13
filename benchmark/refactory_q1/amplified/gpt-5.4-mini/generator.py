def gen(rng):
    n = rng.randint(0, 10)
    if n == 0:
        seq = []
    else:
        vals = [rng.randint(-5, 5) for _ in range(n)]
        seq = sorted(vals)
        if rng.random() < 0.4 and len(seq) > 1:
            seq = sorted(seq[:1] + [seq[0]] * rng.randint(0, 2) + seq[1:])
    choices = []
    if seq:
        choices.extend([
            seq[rng.randrange(len(seq))],
            seq[0] - 1,
            seq[-1] + 1,
        ])
        if len(seq) > 1:
            i = rng.randrange(len(seq) - 1)
            choices.append(seq[i] + (seq[i + 1] - seq[i]) // 2)
    else:
        choices.extend([rng.randint(-5, 5), rng.randint(-5, 5)])
    x = rng.choice(choices)
    return {"args": [x, seq]}