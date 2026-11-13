n= input()
a=0
for i in n:
    if(i=="4" or i=="7"):
        a +=1
b=0
for i in str(a):
    if(i=="4" or i=="7"):
        b+=1
if(b==len(str(a))):
    print("YES")
else:
    print("NO")