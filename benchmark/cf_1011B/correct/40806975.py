import math


def sum():
    y = 0
    ych = 0
    for i in range(len(lc) - 1, -1, -1):
        ych += 1
        if ych > n:
            return y
        y += lc[i] // day
    return y


n, k = map(int, input().split())
l = list(map(int, input().split()))

if n > k:
    print(0)
else:
    l.sort()
    lc = []
    x = 1
    for i in range(0, k - 1):
        if l[i] == l[i + 1]:
            x += 1
        else:
            lc.append(x)
            x = 1
    if x != 1:
        lc.append(x)
    day = 2
    lc.sort()
    while sum() >= n:
        day += 1
    print(day - 1)