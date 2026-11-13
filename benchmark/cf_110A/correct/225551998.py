n=int(input())
c=0
a=0
while(n>0):
    a=n%10
    if a==4 or a==7:
        c+=1
    n=n//10
if c==7 or c==4:
    print("YES")
else:
    print("NO")