x=input()
f=False
for i in range(1,len(x)):
    if x[i].islower():
        f=True
if f==True:
    print(x)
else:
    s=""
    for i in x:
        if i.islower():
            s=s+i.upper()
        else:
            s=s+i.lower()
    print(s)