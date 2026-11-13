from sys import stdin,stdout
from collections import Counter
import math
I=lambda: map(int,stdin.readline().split())
I1=lambda: stdin.readline()

n,m=I()
a=list(I())
x=list(Counter(a).values())
ans=0
for ele in x:
    d=0
    for e in x:
        d+=e//ele
    if d>=n:
        ans=max(ans,ele)
    ans=max(ans,ele//n)
print(ans)