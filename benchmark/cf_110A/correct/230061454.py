n=int(input())
l=0
while n>0:
    if n%10==7 or n%10==4:
        l=l+1
    n=n//10
if l==4 or l==7:
    print("YES")
else:
    print("NO")