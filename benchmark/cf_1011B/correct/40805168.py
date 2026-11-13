from collections import Counter
n, m = [int(x) for x in input().strip().split(' ', 1)]
a = [int(x) for x in input().strip().split(' ')]
s = Counter(a)
mx = int(m / n)
l = 1
r = mx
ans = 0

def ful(x):
    # print(x, sum(int(v / x) for v in s.values()))
    if sum(int(v / x) for v in s.values()) >= n:
        return True
    return False

while l <= r:
    mid = int((l + r) / 2)
    # print(l, r, mid, ful(mid))
    if ful(mid):
        ans = mid
        l = mid + 1
    else:
        r = mid - 1
print(ans)