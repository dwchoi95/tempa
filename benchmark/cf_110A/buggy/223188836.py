n=input()
s=''
for i in n:
    if i=='7' or i=='4':
        s=s+i
    else:
        break
if s==n:
    print('YES')
else:
    print('NO')