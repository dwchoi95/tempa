n=input()
l=len(n)
sum=0
for i in range(l):
    if n[i]=="4" or n[i]=="7":
        sum+=1
if sum==4 or sum==7:
    print("YES")
else:
    print("NO")