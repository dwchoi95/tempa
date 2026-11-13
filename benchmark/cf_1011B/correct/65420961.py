n,m=map(int,input().split())
l=[int(j) for j in input().split()]
d=dict()
for i in l:
    if i in d:
        d[i]+=1
    else:
        d[i]=1
c=[]
for i in d:
    c.append(d[i])
le=0
ri=10**10

while le+1<ri:
    mi=(le+ri)//2
    k=0
    for i in c:
        k=k+i//mi
   
    if k<n:
        ri=mi
    else:
        le=mi
print(le)