n,m=list(map(int,input().split()))
a=list(map(int,input().split()))
a.sort()
l=[]
z=[]
counter=1
l.append(a[0])
for i in range(m):
    if i == 0:
        continue
    if i==m-1 and len(l)==0:
        l.append(counter+1)
        break
    if a[i]==a[i-1]:
        counter+=1
    else:
        l.append(counter)
        counter=1
if len(l)==1:
    print(1)
if len(l)==0:
    print(0)
if len(l)>1:
    for i in range(n):
        z.append(max(l))
        l.remove(max(l))
    print(sum(z)//n)