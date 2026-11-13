from collections import *
rd = lambda: map(int, input().split())
n, m = rd()
a = Counter(rd())
r = 1
while sum(a[x] // r for x in a) >= n:
    r += 1
print(r - 1)