from collections import Counter
n, m = map(int, input().split())
c = Counter(input().split()).values()
d = 1
while sum(ci//d for ci in c) >= n:
    d += 1
print(d - 1)