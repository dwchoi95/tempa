i=int(input())
r=str(i)
f=0
for h in r:
    if h not in '47':
        break
    else:
       f+=1
if len(r)==f:
    print("YES")
else:
    print("NO")