num=int(input())
result=0
count=0
for i in range(len(str(num))):
    a=num%10
    num=num//10
    if a==4 or a==7:    count+=1
for j in range(len(str(num))-1):
    a=num%10
    num=num//10
    if a!=4 and a!=7:
        result=1
if result==1:
    print("NO")
else:
    print("YES")