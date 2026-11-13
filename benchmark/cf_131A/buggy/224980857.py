a=input()
b=len(a)
c=0
for i in range(1,b):
    if ord(a[i])>96:
        print(a)
        c=2
        break
if(c!=2):
    d=a.lower()
    c=list(d)
    c[0]=c[0].upper()
    for i in range(0,b):
        print(c[i],end="")