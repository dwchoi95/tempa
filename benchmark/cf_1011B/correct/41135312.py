'''input
3 9
42 42 42 42 42 42 42 42 42

'''
from collections import Counter

n, m = map(int, input().split())
if n > m:
	print(0)
	quit()
a = list(map(int, input().split()))
d = 1
c = Counter(a).values()
while True:
	s = sum([i//d for i in c])
	if s >= n:
		d += 1
	else:
		break
print(d - 1)