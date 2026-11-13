n=int(input())
c=0
while(n>0):
    if (n%10==4 or n%10==7):
        
        c=c+1
    n=n/10
while(c>0):
    if (c%10!=4 and c%10!=7):
        print ("NO")
        break
    else:
        c=c/10
print("YES")