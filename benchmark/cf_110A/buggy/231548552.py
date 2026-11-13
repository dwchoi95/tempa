a = int(input(''))
s,p = 0,0
while a>1:
    if a%10==4 or a%10==7:
        s+=1
    a=a/10-(a%10/10)
if s==0:
    print("NO")
else:
    while s!=0 and p==0:
        if s%10!=4 and s%10!=7:
            p=1
        s=s/10-(s%10/10)
    if p==0:    
        print("YES")
    else:   
        print("NO")