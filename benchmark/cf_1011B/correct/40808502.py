n, m = map(int, input().split())
div = m//n
a = [int(x) for x in input().split()]
b = {}
c = []
d = 0
for x in a:
    if x not in b:
        b[x] = 1
    else: b[x] += 1
for key, value in b.items():
    c.append(value)
c.sort(reverse=True)
temp = 0
if len(c) > n:
    print(c[n-1])
else:
    while div > 0:
        temp = 0
        for x in c:
            temp += x//div
        if temp >= n:
            break
        else: div -=1
    print(div)