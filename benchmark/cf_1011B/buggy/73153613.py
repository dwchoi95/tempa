def val(x,r,n):
    k=0
    if r==0:
        return 0
    for i in x:
        k+=i//r
    if k>=n:
        return 1
    return 0
    
import bisect as bi 
I = lambda : map(int,input().split())

n, k = I()
a = list(I())
d={}
for i in a:
    d[i]=d.get(i,0)+1
k=sorted(d.values())[::-1]
an=-1;l=0;r=1000
while l<=r:
    mid = (l+r+1)//2
    if not val(k,mid,n):
        r=mid-1
    else:
        l=mid+1
        an=mid
print(an)