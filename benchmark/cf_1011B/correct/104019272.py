from collections import Counter

n, m = map(int,input().split())
c = Counter(input().split())
c = tuple(c.values())
for d in range(1,102):
	if sum(map(lambda x:x//d, c)) < n:
		print(d-1)
		break