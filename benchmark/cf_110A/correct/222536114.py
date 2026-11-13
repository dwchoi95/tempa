n=int(input())
c=0
while n>0:
    if n%10==4 or n%10==7:
        c+=1
    n//=10
if c==4 or c==7:
    print("YES")
else:
    print("NO")