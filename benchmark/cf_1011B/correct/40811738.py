from collections import Counter
n,k = map(int,input().split(" "))
l = [int(c) for c in input().split(" ")]
d = list(Counter(l).values())
if k<n:
    print(0)
else:
    m = k//n
    p=0
    for i in range(1,m+1):
        s = 0
        for j in d:
            s += j//i
        if s>=n:
            p=i
        else:
            break
    print(p)