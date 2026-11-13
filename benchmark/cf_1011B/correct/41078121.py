from collections import defaultdict as dd

d = dd(int)
n, k = [int(i) for i in input().split(" ")]
l = [int(i) for i in input().split(" ")]

for i in l:
    d[i] += 1
m = sorted(d.values())

if sum(l) < n:
    print(0)
else:
    ans = 0
    for x in range(1, 10000):
        p = 0
        for i in m:
            p += i // x
        if p >= n:
            ans = x
            
    print(ans)