def bs(mid,a,z):
    if sum(i//mid for i in z)>=a:
        return 1
    return 0
a,b=map(int,input().split())
z1=dict()
for i in map(int,input().split()):
    z1[i]=z1.get(i,0)+1
z=list(z1.values())
lo=1;hi=100;ans=0
while(lo<=hi):
    mid=lo+(hi-lo)//2
    if (bs(mid,a,z)):
        ans=mid
        lo=mid+1
    else:
        hi=mid-1
print(ans)