a, b = map(int, input().split())
l = sorted(list(map(int, input().split())))
m = set()
for i in l:
	m.add(i)
k = {}
for i in m:
	k[i]=l.count(i)
c = 0
for i in range(1, 101):
	y = 0
	for j in k:
		y += k[j]//i
	if y >= a:
		c += 1
	else:
		break
print(c)