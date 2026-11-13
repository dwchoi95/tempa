n=int(input())
c=0
while n>0:
    k=n%10
    n=n//10
    if k==4 or k==7:
        continue
    else:
        c=1
        break
    
if c==0:
    print("YES")
else:
    print("NO")