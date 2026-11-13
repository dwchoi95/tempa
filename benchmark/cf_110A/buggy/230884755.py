s=input()
count=0
for i in s:
    if i=='4' or i=='7':
        count+=1
if (count%7==0 or count%4==0) and count!=0:
    print('YES')
else:
    print('NO')