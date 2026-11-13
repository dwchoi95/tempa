from collections import Counter
from operator import itemgetter
n, m = map(int, input().split())
packs = Counter(map(int, input().split()))
l = sorted(packs.items(), key = itemgetter(1), reverse=True)
#print(l)
if m<n:
    print(0)
else:
    a = 1
    b = l[0][1]+1
    while b>a+1:
        c = (a+b)//2
        num = sum([p[1]//c for p in l])
        #print(f"a={a}, b={b}, testing c={c}: enough for {num} days")
        if num>=n:
            a = c
        else:
            b = c
    print(a)