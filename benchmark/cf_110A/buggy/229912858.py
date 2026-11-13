a=int(input())
cnt=0
while(a>0):
    if(a%10==4 or a%10==7):
        cnt=cnt+1
    a=int(a/10)
b=True
while(cnt>0):
    if(cnt%10!=4 and cnt%10!=7):
        b=False
        print("NO")
        break
    cnt=int(cnt/10)
if(b==True):
    print("YES")