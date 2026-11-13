a=input()
l=list(a)
c=0
for i in l:
    if i!='4' and i!='7':
        c=c+1
    else:
        continue
if c==0:
    print("YES")
else:
    print("NO")