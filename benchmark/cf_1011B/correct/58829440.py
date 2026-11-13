n,k=map(int,input().split())
a=list(map(int,input().split()))
hsh=[0]*max(a)
for i in a:
    hsh[i-1]+=1
ans=0
for i in range(1,k+1):
    cnt=0
    for j in hsh:
        cnt+=(j//i)
    if(cnt>=n):
        ans=i
print(ans)