n=int(input())
count=0
while n>0:
    digit=n%10
    if digit==4 or digit==7:
        count+=1
    n//=10
nearly=0
while count>0:
    digit=count%10
    if digit!=4 and digit!=7:
        print("NO")
        exit()
    count//=10
    nearly+=1
if nearly==0:
    print("NO")
else:
    print("YES")