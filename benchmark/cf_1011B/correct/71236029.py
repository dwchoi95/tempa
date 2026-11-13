from collections import Counter

I = lambda: map(int, input().split())

n, _ = I()
V = Counter(I()).values()
d = 1

while sum(v//d for v in V) >= n:
    d += 1

print(d-1)