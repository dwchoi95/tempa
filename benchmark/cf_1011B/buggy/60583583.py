n, m = map(int, input().split())
packs = [int(m) for m in input().split()]
d = {}
for p in packs:
    if p not in d:
        d[p] = 1
    else:
        d[p] += 1
print(sum(d.values())//n)