n=input()
l=len(n)
count=0
for i in range(0,l):
    if(n[i]==4 or n[i]==7):
        count=count+1
if(count==l and (count==4 or count==7)):
    print("YES")
else:
    print("NO")