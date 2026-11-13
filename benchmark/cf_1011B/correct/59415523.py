p,w=input().split()
p=int(p)
w=int(w)
f=input().split()
f=[int(i) for i in f]
n={}
for i in f:
    n[i]=0
for i in f:
    n[i]+=1
d=1
while True:
    z=0
    for j,i in n.items():
       z+=(i//d)
    if z<p:
        d=d-1
        break
    d+=1
print(d)