from sys import stdin
def input(): return stdin.readline()
ans=0
flag=True
s=int(input())
while(s>0):
    a=s%10
    if(a==4 or a==7):
        ans=ans+1
    s=s/10
    s=int(s)
print(ans)
while(ans>0):
    a=ans%10
    print(a)
    if(a!=4 and a!=7):
        print("NO")
        flag=False
    ans=ans/10
    ans=int(ans)
if(flag):
    print("YES")