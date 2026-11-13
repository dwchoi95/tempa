n,m=map(int,input().split())
l=list(map(int,input().split()))
d={}
d=d.fromkeys(l,0)
for i in l:
    d[i]=d.get(i)+1
x=list(d.values())
x.sort()
s=0
for i in range(len(x)):
    s=s+x[len(x)-i-1]
    if s/n < x[len(x)-i-1]:
        continue
    else:
        break
print(int(s/n))