a=input()
t=0
if a==4 or a==7:
    print("NO")
for i in a:
    if i!='4' and i!='7':
        t=t+1
        break
if t==0:
    print("YES")
else:
    print('NO')