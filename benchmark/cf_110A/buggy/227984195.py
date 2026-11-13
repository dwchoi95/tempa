s=input()
flag=False
for i in s:
    if i!='4' or i!='7':
        flag=False
    else:
        flag=True
if flag:
    print("YES")
else:
    print("NO")