from collections import*
R=lambda:map(int,input().split())
n,m=R()
a=Counter(R()).values()
i=1
while sum(x//i for x in a)>=n:i+=1
print(i-1)