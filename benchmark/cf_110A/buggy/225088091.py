t=int(input())
t=str(t)
ans=0
for i in t:
    if i=='4' or i=='7':
        ans+=1
flag=True
while ans:
    rem=ans%10
    if rem!=4 and rem!=7:
        flag=False
        break
    ans//=10
if flag:
    print('YES')
else:
    print('NO')