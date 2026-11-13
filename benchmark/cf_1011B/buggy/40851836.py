n=list(map(int,input().split()))
t=list(map(int,input().split()))
tx=set(t)

def check(x):
    z=0
    for i in tx:
        z+=z/x
    return z



maxi=[]
for i in tx:
    a=check(t.count(i))
    if(a>=n[0]):maxi.append(a)

if len(maxi)==0:print(0)
else: print(maxi[len(maxi)-1])