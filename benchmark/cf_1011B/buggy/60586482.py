n, m = map(int, input().split())
packs = [int(m) for m in input().split()]
d = {}
def gcd(a, b):
    if b == 0:
        return a
    return gcd(b, a % b)
for p in packs:
    if p not in d:
        d[p] = 1
    else:
        d[p] += 1
fin = 0
if len(d.keys()) == 1:
    fin = sum(d.values())//n
else:
    for v in sorted(list(d.values()), reverse=True):
        temp = v
        break
    tot = 0
    past_v = 0
    for v in sorted(list(d.values()), reverse=True):
        temp = gcd(temp, v)
        tot = tot + v
        if tot >= temp * n:
            fin = temp
            break
        elif (tot-past_v) // n > v:
            fin = (tot - past_v)//n
        past_v = v
if fin == 0:
    fin = tot//n
print(fin)