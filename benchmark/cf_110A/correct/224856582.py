lucky_number_count=0
n=list(input())
for i in n:
    if i=='4' or i=='7':
        lucky_number_count+=1
if  lucky_number_count==4 or lucky_number_count==7:
    print('YES')
else:
    print('NO')