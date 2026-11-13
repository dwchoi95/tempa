m, n = map(int, input().split())
a = [int(s) for s in input().split()]
d = {}
for elem in a:
    if elem in d.keys():
        d[elem] += 1
    else:
        d[elem] = 1
maxi = d[a[0]]
for elem in d.keys():
    if d[elem] > maxi:
        maxi = d[elem]
print(min(n//m, maxi))