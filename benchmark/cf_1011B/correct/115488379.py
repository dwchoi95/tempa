def check(t,dict):
    count=0
    for i in dict:
        count+=dict[i]//t
    return count
nm=input().split()
n,m=int(nm[0]),int(nm[1])
a=list(map(int,input().split()))
dict={}
for i in a:
    if i in dict:
        dict[i]+=1
    else:
        dict[i]=1
maxx=-1
for i in dict:
    if dict[i]>maxx:
        maxx=dict[i]
ans=-1
low,high=1,maxx
while(low<=high):
    mid=(low+high)//2
    if check(mid,dict)>=n:
        ans=mid
        low=mid+1
    else:
        high=mid-1
if ans==-1:
    print(0)
else:
    print(ans)