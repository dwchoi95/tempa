n,m=map(int,input().split())
a=list(map(int,input().split()))

c={}
for x in a:
    c[x]=c.get(x,0)+1

ans=n
while True:
    if ans==0:break
    if sum(c[i]//ans for i in c)<n:
        ans-=1
    else:
        break
print(ans)