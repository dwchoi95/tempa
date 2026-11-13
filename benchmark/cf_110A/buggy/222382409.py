n=int(input())
s=set(str(n))
k='47'
c=c1=0
for i in s:
    if i in k:
        c+=1
    else:
        c1+=1
if(c==2 and c1==0):
    print("YES")
else:
    print("NO")