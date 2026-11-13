n=7745
c=0
d=0

while(n):
    r=n%10
    if(r==7 or r==4):
        c+=1
    d+=1
    n//=10
    
if(c==d):
    print("yes") 
else:
    print("no")