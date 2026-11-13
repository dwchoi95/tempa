from collections import defaultdict
n, m = map(int, input().split())
a = list(map(int, input().split()))
rec = defaultdict(int)
for i in range(m):
    rec[a[i]] += 1


def ok(k):
    if k == 0:
        return False
    tmp = 0
    for i in rec.values():
        tmp += i // k

    return tmp >= n


left, right = 0, 10000
p = 0
while p < 1000:
    mid = (left + right) // 2
    q = ok(mid)

    if q:
        left = mid
    else:
        right = mid

    p += 1

print(mid)