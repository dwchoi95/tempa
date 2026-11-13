import collections as cc
n,m=map(int,input().split())
l=list(map(int,input().split()))
ff=cc.Counter(l)
ff=dict(ff)
i=1
ans=0
while  i:
    temp=0
    for j in ff.values():
        temp+=j//i
    if temp>=n:
        ans=i
    else:
        break
    i+=1
print(ans)