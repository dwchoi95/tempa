n, m = map(int, input().split())
a, a_sorted, d = sorted(list(map(int, input().split()))), [], int(m/n)
for i in range(len(set(a))):
	for j in range(a.count(list(set(a))[i])):
		a_sorted.append(list(set(a))[i])


while True:
    i, x = 0, 0
    while x < n and i < len(a_sorted):
        if i+d <= len(a_sorted) and len(set(a_sorted[i:i+d])) == 1:
            i += d
            x += 1
        else:
            i += 1
    if x < n and d != 0:
        d -= 1
    else:
        break

print(d)