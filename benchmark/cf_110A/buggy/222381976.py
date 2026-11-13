n=int(input())
s=str(n)
k='47'
c=0
for i in s:
    if i not in k:
        c+=1
if(c>0):
    print("NO")
else:
    print("YES")