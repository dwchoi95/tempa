n=int(input())
n=str(n)
f=0
for i in n:
    if i!='4' and i!='7':
        f=1
        break
if f:
    print("NO")
else:
    print("YES")