def scanf(obj=list, type=int, sep=' '):
    return obj(map(type, input().split(sep)))
n, m = scanf()
v = scanf()
t = [0] * 101
for x in v: t[x] += 1
for i in range(100, 0, -1):
    if sum([x//i for x in t]) >= n:
        print(i)
        break
else: print(0)