n=int(input())
c=0
while(n):
    r=n%10
    if(r==4 or r==7):
        c+=1
    n=n//10
if c%4==0 or c%7==0:
    print("YES")
else:
    print("NO")