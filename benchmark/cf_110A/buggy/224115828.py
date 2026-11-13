i=int(input())
r=str(i)
f=0
for h in r:
    if h in ('4','7'):
        f+=1
    else:
        break
if len(r)==f:
    print("YES")
else:
    print("NO")