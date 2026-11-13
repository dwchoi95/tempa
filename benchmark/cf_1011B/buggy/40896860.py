n,m=map(int,input().split())
l=list(map(int,input().split()))
d={}
d=d.fromkeys(l,0)
for i in l:
    d[i]=d.get(i)+1
x=list(d.values())
x.sort()
k=1
u=0
while(k):
    newList = [ int(t / k) for t in x ]
    if sum(newList)<n:
        u=1
        break
    elif sum(newList)==n:
        u=2
        break
    else:
        k=k+1
print(k if u==2 else k-1)