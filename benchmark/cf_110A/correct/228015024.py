x=str(input())
sum=0
for i in x:
    if i=='7' or i=='4':
        sum+=1
if sum==7 or sum==4:
    print('YES')
else:
    print('NO')