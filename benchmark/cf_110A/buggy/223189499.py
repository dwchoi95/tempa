n=input()
s=0
for i in n:
    if i=='7' or i=='4':
        s=s+1
    else:
        break
if s==4 or s==7:
    print('YES')
else:
    print('NO')