n=int(input())
c=0
r=0
while n>0:
    r=int(n%10)
    n=int(n/10)
    #print(r,n)
    if r!=4 and r!=7:
        print("NO")
        c=0
        break
    else:
        c=1
if c==1:
    print("YES")