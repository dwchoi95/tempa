n=input()
count=0
for i in n:
    if i !='4' and i !='7':
        count+=1
    elif i=='4' or i=='7':
        count+=0
if count!=0:
        print('NO')
else:
        print('YES')