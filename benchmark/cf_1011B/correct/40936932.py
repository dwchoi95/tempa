n,m=map(int,input().split())
c={}
for x in map(int,input().split()):c[x]=c.get(x,0)+1
ans=1
while sum(c[i]//ans for i in c)>=n: ans+=1
print(ans-1)