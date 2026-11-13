lucky_number_count=0
judge=True
n=list(input())
for i in n:
    if i=='4' or i=='7':
        lucky_number_count+=1
    else:
        judge=False
if  lucky_number_count==4 or lucky_number_count==7:
    print('YES')
elif judge==True:
    print('YES')
else:
    print('NO')