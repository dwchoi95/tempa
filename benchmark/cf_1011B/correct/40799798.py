n, m = map(int, input().split())
a = [int(x) for x in input().split()]
d = dict.fromkeys(list(set(a)), 0)
for x in a:
    d[x] += 1
#print(d)

days = 1
fit = True

while fit:
    s = 0
    for x in d.keys():
        s += d[x] // days
    if s >= n:
        days += 1
    else:
        fit = False
        days -= 1

print(days)