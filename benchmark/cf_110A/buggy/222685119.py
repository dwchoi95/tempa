n=int(input())
c=0
r=0
while n>0:
    r=int(n%10)
    n=int(n/10)
    #print(r,n)
    if r==4 or r==7:
        c=1+c

if c==4 or c==7 or c==47 or c==74 or c==44:
    print("YES")
else:
    print("NO")