a=input()
l=[i for i in a]
c=0
for i in range(0,len(a)):
    if l[i]=='4' or l[i]=='7':
        c=c+1 
if c==len(a):
    print("YES")
else:
    print("NO")