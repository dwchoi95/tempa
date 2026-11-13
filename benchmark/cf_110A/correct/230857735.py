n=str(input())
count=0
for i in n:
    if i == '4' or i == '7':
        count+=1

y=str(count)
f=0
z=str(count)
x=len(z)
for j in y:
    if j == '4' or j == '7':
        f+=1
    
if f==x:
    print("YES")
else:
    print("NO")