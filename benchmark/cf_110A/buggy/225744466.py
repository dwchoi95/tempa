n=input()
count1=0
count2=0
for i in n:
    if i =='4':
        count1+=1
    elif i=='7':
        count2+=1
if count1>=1 and count2>=1:
        print('YES')
else:
        print('NO')