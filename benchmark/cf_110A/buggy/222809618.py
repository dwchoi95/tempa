s=input()
c=0
for i in s:
    if i!=4 and i!=7:
        c=c+1
if c==0:
    print("YES")
else:
    print("NO")