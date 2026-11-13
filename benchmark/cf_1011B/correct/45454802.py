n, m = map(int, input().split())
a = map(int, input().split())

counts = { }

for i in a:
    counts[i] = counts.setdefault(i, 0) + 1

l = 0
r = m // n

while l < r:
    m = (l + r + 1) // 2
    
    s = 0
    for v in counts.values():
        s += v // m

    if s >= n:
        l = m
    else:   
        r = m - 1

print(l)