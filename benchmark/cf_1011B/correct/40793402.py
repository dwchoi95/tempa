n, k = map(int, input().split())
d = {}
for e in input().split():
    if e not in d:
        d[e] = 0
    d[e] += 1
a = list(d.values())
l = 0
r = k + 1
while r - l > 1:
    m = (l + r) // 2
    if sum([e // m for e in a]) >= n:
        l = m
    else:
        r = m
print(l)