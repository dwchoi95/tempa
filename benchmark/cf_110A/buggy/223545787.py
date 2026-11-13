n=input()
l=0
flag=True

for i in n:
    if i=='4'or i=='7':
        l+=1
    else:
        flag=False

if(l==len(n)) or flag:
    print("YES")
else:
    print("NO")