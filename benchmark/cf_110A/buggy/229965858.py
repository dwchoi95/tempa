n=input()
k=len(n)
v=0
for i in n:
   if i==4 or i==7:
       v+=1
if k==v:
    print("YES")
else:
    print("NO")