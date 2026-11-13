lis=[4,7]

x=int(input())
sum=0

while x>0:
    y=x%10
    x=x//10
    if y in lis:
       sum+=1

if sum in lis:
    print("YES")
else:
    print('NO')