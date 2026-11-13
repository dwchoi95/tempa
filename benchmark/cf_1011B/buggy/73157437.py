n,k=map(int,input().split())
a=list(map(int,input().split()))
d={}
for i in a:
    if(i in d):
        d[i]+=1
    else:
        d[i]=1
count=0
b=k//n
while(b>0):
    for i in sorted(d.keys()):
        if(d[i]>=b):
            temp=d[i]//b
            n=n-temp
        if(n==0):
            count=1
            break
    if(count==1):
        break
    b-=1
print(b)