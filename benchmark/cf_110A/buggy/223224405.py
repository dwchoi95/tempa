a=int(input())
c=0
k=0
while(a):
    k+=1
    a=a//10
if(k==4 or k==7):
    while(a>0):
        if(a%10==4 or a%10==7):
                 c+=1
                 a=a//10
if(c==4 or c==7):
    print("YES")
else:
    print("NO")