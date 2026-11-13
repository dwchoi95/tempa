n=int(input())
c=0
while(n>0):
    
    if (n%10==4 or n%10==7):
        
        c=c+1
    n=n//10

if (c==7 or c==4):
    
    print("YES")
    
else:
    print("NO")