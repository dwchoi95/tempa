n = int(input())
f = 0
while n>0:
    d = n%10
    if d!=4 and d!=7:
        f = 1
    n=int(n/10)
if f==0:
    print("YES")
else:
    print("NO")