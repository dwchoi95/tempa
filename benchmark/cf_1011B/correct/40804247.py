from collections import defaultdict
n,m=map(int,input().split())
l=list(map(int,input().split()))
d=defaultdict(int)
l1=[0]
for i in range(len(l)):
    d[l[i]]+=1
for i in range(1,101):
    l1.append(int(d[i]))
#print(l1)
p=k=0
#print(l1)
l1=sorted(l1)
if(m<n):
    print("0")
    exit(0)
#print(len(l1))
for i in range(1,101):
    k=0
    for j in range(100,100-n,-1):
        if(int(l1[j])//i>0):
            k+=int(l1[j])//i
    if(k>=n):
        p=max(i,p)
print(p)