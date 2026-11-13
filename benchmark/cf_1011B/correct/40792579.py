n, m = [(int)(x) for x in input().split(' ')]
types = [(int)(x) for x in input().split(' ')]

packs = [0] * 128
for tt in types:
	packs[tt] += 1

best = 0
for days in range(1, 1024):
	support = 0
	for p in packs:
		support += p // days

	if support >= n:
		best = days

print(best)