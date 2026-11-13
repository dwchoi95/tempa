n,m=[int(x) for x in input().split()]
a=list(map(int,input().split()))
if n==m:
    print(1)
    exit()
d=dict()
v=[]
for i in range(101):
    d[i]=0
for i in range(m):
    d[a[i]]+=1
for i in range(101):
    if d[i]:
        v.append(d[i])
v.sort()
maxa=0
if len(v)==1:
    print(v[0]//n)
    exit()
for i in range(0,len(v)):
    num=v[i]
    for k in range(1,num+1):
        c=0
        c+=(num//k)
        for j in range(i+1,len(v)):
            c+=v[j]//k
            if c>=n and k>maxa:
                maxa=k
        
        
print(maxa)