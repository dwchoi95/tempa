s=input()
a="47"
c=0
for i in s:
        if(i=="4" or i=="7"):
                c+=1
c=str(c)
k=0
for j in c:
        if(j in a):
                k+=1
if(len(c)==k):
        print("YES")
else:
        print("NO")