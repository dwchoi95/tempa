from sys import stdin,stdout
from collections import Counter
import math
I=lambda: map(int,stdin.readline().split())
I1=lambda: stdin.readline()

n,m=I()
a=list(I())
x=Counter(a).values()
print(x)
ans=1
while sum(y//ans for y in x)>=n:
    ans+=1 
print(ans-1)