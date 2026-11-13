n=list(input())
f=map(int,n)
m=0
for i in f:
    if i==4 or i==7:
        m+=1

t=list(str(m))
q=map(int,t)
for s in q:
    if s!=4 and s!=7:
        print("NO")
        break
    else:
        print("YES")