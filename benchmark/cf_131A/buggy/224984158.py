a=input()
b=bool(True)
c=len(a)
d=a.lower()
for i in range(0,c):
    if (ord(a[i])>96):
        b=False
if (b==True):
    print(d)
else:
    if(ord(a[0])<97):
        print(a)
    else:
        d=list(d)
        d[0]=d[0].upper()
        for i in range(0,c):
            print(d[i],end="")