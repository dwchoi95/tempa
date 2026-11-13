def rec(l, r):
    global b
    global m
    if l + 1 >= r:
        return l if l != -1 else 0
    m2 = (l + r) // 2
    i = 0
    c = 0
    while i != len(b) and c < n and b[i] >= m2 and m2 != 0:
        c += b[i] // m2
        i += 1
    if c < n and m2 != 0:
        return rec(l, m2)
    return rec(m2, r)


n, m = map(int, input().split())
a = [int(i) for i in input().split()]
b = []
for item in set(a):
    b.append(a.count(item))
b.sort(reverse=True)
print(rec(-1, b[0] + 1))