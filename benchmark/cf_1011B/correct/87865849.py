def bs(mid,a,z1):
    #print(mid,z)
    i=0;k=0;z=z1.copy();f=0
    while(i<len(z)):
        if z[i]>=mid:
            while z[i]>=mid:
                f+=1
                z[i]-=mid
        else:
            i+=1
    if f>=a:
        return 1
    return 0
a,b=map(int,input().split())
z1=dict()
for i in map(int,input().split()):
    z1[i]=z1.get(i,0)+1
z=sorted(z1.values(),reverse=True)
lo=1;hi=100;ans=0
while(lo<=hi):
    mid=lo+(hi-lo)//2
    if (bs(mid,a,z)):
        ans=mid
        lo=mid+1
    else:
        hi=mid-1
print(ans)