n=input()
m=False
for i in n:
    if n!='7':
        if i=='4' or i== '7':
            m=True
        else:
            m=False
            break
if m==True:
    print("YES")
else:
    print("NO")