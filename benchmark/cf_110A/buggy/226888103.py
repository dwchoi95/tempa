n=int(input())
c=0
c4=0
c7=0
while n>0:
    k=n%10
    n=n//10
    if k==4:
        c4=c4+1
    elif k==7:
        c7=c7+1
    else:
        c=1
        break
    
if c==0 and c4>0 and c7>0:
    print("YES")
else:
    print("NO")