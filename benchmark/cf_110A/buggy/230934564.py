from sys import stdin
def input(): return stdin.readline()
ans=0

flag=True
s=input()
i=0
while(i<len(s)-1):
    a=int(s[i])
    if(a==4 or a==7):
        ans=ans+1
    i=i+1
if(ans==0):
    print("NO")
    flag=False
print(ans)
while(ans>0):
    a=ans%10
    if(a!=4 and a!=7):
        print("NO")
        flag=False
    ans=ans/10
    ans=int(ans)
if(flag):
    print("YES")