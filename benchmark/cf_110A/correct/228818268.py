a=int(input())
s=0
while a>0:
    e=a%10
    if e==4 or e==7:
        s=s+1
    a=a//10
if s==4 or s==7:
    print("YES")
else:
    print("NO")