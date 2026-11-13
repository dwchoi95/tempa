s=input()
c=0
c1=0
c2=0
for i in s:
    if i=='4' or i=='7':
        c+=1
for i in s:
    if i=='4':
        c2+=1
    elif i=='7':
        c1+=1
if c==len(s) and c1>=1 and c2>=1 :
    print("YES")
else:
    print("NO")