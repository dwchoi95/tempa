a = {3, 1, 2, 100, -5, 2**61, 1.5, None, (1, 2)}
b = set([9, 8, 7, 64, 33, 1])
print(a, b, a | b, a & b, a - b, b - a, a ^ b)
b.discard(64); b.add(17); b |= {200, 5}; print(b, list(b), b.pop(), b)
c = {x * 7 % 40 for x in range(30)}
print(c, sorted(c)[:3], len(c), 14 in c)
d = set()
for i in range(50, 0, -3):
    d.add(i)
d -= {2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32}
print(d, frozenset([4, 2]))
