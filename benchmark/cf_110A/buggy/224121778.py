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
for k,v in d.items():
    if k=='4' and '7' and v>=1:
        f+=1
    else:
        f=0
if f>=1:
    print("YES")
else:
    print("NO")