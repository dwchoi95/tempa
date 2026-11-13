n=int(input())
count=0
while n!=0:
    a=n%10
    if a==4 or a==7:
        count+=1
    n=n//10
if count==4 or count==7:
    print("YES")
else:
    print("NO")