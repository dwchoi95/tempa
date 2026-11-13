n=int(input())
x=str(n)
d=0
for i in range(len(x)):
    c=n%10
    n=n//10
    if(c==7 or c==4):
        d=d+1

if(d==7 or d==4):
    print("YES")
else:
    print("NO")