n, m = map(int, input().split())

packages = list(map(int, input().split()))

counts = dict()

for p in packages:
	if p in counts:
		counts[p] += 1
	else:
		counts[p] = 1

arrayCounts = []
for package, count in counts.items():
	arrayCounts.append(count)

arrayCounts.sort()
arrayCounts.reverse()

for i in range(m//n+1):
	days = i+1
	people = 0
	for type in arrayCounts:
		people += type//days
	if people < n:
		break

print(i)