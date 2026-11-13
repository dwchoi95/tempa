i=int(input())
u=str(i)
d={}
for r in u:
    if r in d.keys():
        d[r]+=1
    else:
        d[r]=1
dd={}
for k,v in d.items():
    if k=='4' or k=='7':
        dd[k]=1
    else:
        dd[k]=1
f=0
for b in dd.keys():
    if k=='4':
        f+=1
    elif k=='7':
        f+=1
if f==2:
    print("YES")
else:
    print("NO")