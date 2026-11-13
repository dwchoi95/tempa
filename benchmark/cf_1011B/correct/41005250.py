n, m = map(int, input().split())
a = {}
for i in map(int, input().split()):
    if not i in a:
        a[i] = 0
    a[i] += 1
l, r = 0, m
while l != r:
    k = (l + r + 1) // 2
    if k == 0:
        p = n
    else:
        p = sum([y // k for x, y in a.items()])
    if p >= n:
        l = k
    else:
        r = k - 1
print(l)