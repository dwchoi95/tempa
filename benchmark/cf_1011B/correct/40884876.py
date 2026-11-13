n,k=[int(x) for x in input().split()]
a=[int(x) for x in input().split()]
m=[0]*101
for i in a:
    m[i]+=1
fin=[]
for i in m:
    if i!=0:
        fin.append(i)
fin.sort()
ans=0

d=1
flag=0
while(flag!=1):
    p=0
    for i in fin:
        p+=i//d
    
    if p<n:
        break
    ans=d
    d+=1
print(ans)