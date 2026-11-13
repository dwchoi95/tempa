a=input()
t=0
if a=="4" or a=="7":
    print("NO")
else:
    for i in a:
        if i=='4' and i=='7':
            t=t+1
if t==4 or a==7:
    print('YES')
else:
    print('NO')