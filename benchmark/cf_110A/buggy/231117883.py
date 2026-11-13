n=4407
c=0
d=0
 
while(n):
    r=n%10
    if(r==7 or r==4):
        c+=1
    n//=10
    
if(c==4 or c==7):
        print("YES") 
else:
    print("NO")