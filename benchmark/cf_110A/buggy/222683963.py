n=int(input())
c=0
r=0
while n:
    r=n%10
    n=n/10
    if r!=4 or r!=7:
        print("NO")
        c=0
        break
    else:
        c=1
if c==1:
    print("YES")