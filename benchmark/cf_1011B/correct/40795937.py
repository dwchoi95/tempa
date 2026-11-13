n, m = map(int, input().split())
K = list(map(int, input().split()))
D = dict()
for i in range(m):
    if K[i] in D.keys():
        D[K[i]] += 1
    else:
        D[K[i]] = 1

ans = 0
for days in range(1, 102):
    h = 0
    for i in D.values():
        h += i // days
    if h >= n:
        ans = days
    else:
        break
print(ans)