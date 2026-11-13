a,b=map(int,input().split())
c=list(map(int,input().split()))
s=[0]*(max(c)+1)
for i in range(b):
    s[c[i]]+=1  
l=0
r=10**9
k=0
while l!=r:
    k=0
    m=(l+r)//2
    for i in range(max(c)):
        if s[i]!=0:
            k+=s[i]//m
    if k>a:
        l=m+1
    else:
        r=m
print(l)