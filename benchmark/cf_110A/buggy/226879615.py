n = int(input())
unluck = [1,2,3,5,6,8,9,0]
luck = [4,7]
temp = n
digits=[]
while temp>0:
    digits.append(temp%10)
    temp = temp//10
flag=1
for i in unluck:
    c=0
    if i in digits:
        c=c+1
        flag=0
if flag==0:
    if c==4 or c==7:
        print("YES")
    else:
        print("NO")
else:
    print("YES")