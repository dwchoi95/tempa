n,m=map(int,input().split())
a=[int(x) for x in input().split()]
na=[0]*101
a.sort()
f=0
for i in range(m):
    na[a[i]]+=1
for i in range(100,0,-1):
    k=0
    nna=[]
    for x in range(len(na)):
        nna.append(na[x])
    #print(nna,na)
    for j in range(1,101):
        while(nna[j]>=i):
            k+=1
            nna[j]-=i
    if(k>=n):
        print(i)
        f=1
        break
if(f==0):
    print(0)