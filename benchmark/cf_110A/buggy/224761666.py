first_line=input()
flag=0
for i in first_line:
    if i !='7' and i !='4':
        flag = 1
        break
if flag ==0 :
    print ('YES')
else:
    print('NO')