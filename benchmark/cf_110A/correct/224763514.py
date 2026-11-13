first_line=input()
counter= 0
for i in first_line:
    if i =='7' or i =='4':
        counter+=1
        
if counter==4 or counter == 7:
    print ('YES')
else:
    print('NO')