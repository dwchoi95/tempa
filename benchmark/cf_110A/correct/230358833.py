n=int(input())
ans=0
while n>0:
    r=n%10
    if r==4 or r==7:
        ans+=1 
    n=n//10 
if ans==4 or ans==7:
    print("YES")
else:
    print("NO")