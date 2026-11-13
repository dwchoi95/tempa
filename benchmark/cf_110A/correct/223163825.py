a=input()
l=list(a)
c=0
for i in l:
    if i in '47':
        c=c+1
    else:
        continue
if c==4 or c==7:
    print("YES")
else:
    print("NO")