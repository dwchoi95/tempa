n=int(input())
n=str(n)
sum=0
for i in n:
    if int(i)==4 or int(i)==7:
        sum+=1
    else:
        continue
if sum==4 or sum==7:
    print("YES")
else:
    print("NO")