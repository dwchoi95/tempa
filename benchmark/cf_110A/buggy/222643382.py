n = int(input())
c = 0
while n>0:
    d = n%10
    if d==4 or d==7:
        c = c+1
    n=int(n/10)
if c==4 or c==7:
    print("YES")
else:
    print("NO")