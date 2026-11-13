a=int(input())
b=True
while(a>0):
    if(a%10!=4 and a%10!=7):
        b=False
        print("NO")
        break
    a=int(a/10)
if(b==True):
    print("YES")