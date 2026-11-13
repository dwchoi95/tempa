n=input()
l=len(n)
count=0
for i in range(0,l):
    if(n[i]==4 or n[i]==7):
        count=count+1
if(count==7 or count==4 or count==l):
    print("YES")
else:
    print("NO")