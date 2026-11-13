a=int(input())
b="47"
a=str(a)
c=0
for i in a:
    if i in b:
        c=c+1
if c==len(a):
    print("YES")
else:
    print("NO")