from collections import Counter
n, m = list(map(int, input().split()))
a = input().split()
c = Counter(a)
freqs = []
for i in c.keys():
	freqs.append(c[i])
freqs.sort(reverse=True)
for days in range(100, 0, -1):
	done = 0
	for i in freqs:
		done += i // days
	if done >= n:
		print(days)
		break
else:
	print(0)