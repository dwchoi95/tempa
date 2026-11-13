n, m = map(int, input().split())
a = list(map(int, input().split()))
rec = {}
for i in range(n):
    rec[a[i]] = rec.get(a[i], 0) + 1

r = 1
while True:
    q = 0
    for i in rec.values():
        q += i // r

    if q < m:
        break

print(r - 1)