n=input()
f=0
if n=='7':
    print("NO")

for i in n:
    if i!='4' and i!='7':
        f=1
if f==0:
    print("YES")
else:
    print("NO")