n=input()
s=len(n)
count=0
for i in range(0,s-1):
    if(n[i]==4 or n[i]==7):
        count=count+1
        
if(count==4 or count==7):
    print("YES")
else:
    print("NO")