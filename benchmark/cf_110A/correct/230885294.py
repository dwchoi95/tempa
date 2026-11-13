s=input()
count=0
flag=1
for i in s:
    if i=='4' or i=='7':
        count+=1
count=str(count)
for i in count:
    if i!='7' and i!='4':
        flag=0
        break
if flag==1:
    print('YES')
else:
    print('NO')