import sys
n, m = map(int, input().split())
L = [int(el) for el in input().split()]
L.sort()
L1 = []
L1.append(L.count(L[0]))
for i in range(1, len(L)):
    if L[i] != L[i - 1]:
        L1.append(L.count(L[i]))
zn = 0
for i in range(1, 1000):
    p = n
    for el in L1:
        if el >= i:
            p -= el // i
    if p <= 0:
        zn = i
    if p > 0:
        print(zn)
        sys.exit()