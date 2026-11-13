i=int(input())
t=0
f=str(i)
for j in f:
    if j in '47':
        t+=1
    else:
        pass
if t==len(f):
    print("YES")
else:
    print("NO")