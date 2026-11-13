def mi():
	return map(int, input().split())

n,m = mi()
from collections import Counter
a = Counter(list(mi()))
if m<n:
	print (0)
else:
	b = []
	for i in a:
		b.append(a[i])
	b.sort(reverse=True)
	l = 0
	for i in range(1,101):
		k = 0
		for j in b:
			if j//i >0:
				k+=j//i
		if k>=n:
			l = max(i,l)
	print (l)