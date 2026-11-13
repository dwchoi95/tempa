import itertools
n, k = [int(x) for x in input().split()]
a = [int(x) for x in input().split()]
f = [a.count(f) for f in range(1,101)]
f.sort(reverse=True)
f = f[0:f.index(0)]
for d in range(f[0], -1, -1):
    if d == 0:
        print(d)
        break
    tkwf = 0
    for kt in f:
        tkwf += kt // d
    if tkwf >= n:
        print(d)
        break