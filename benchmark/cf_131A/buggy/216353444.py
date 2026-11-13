s=input()
c=0
for i in s:
    if i.lower() == i:
        c+=1
if c<1:
    print(s.title())
elif c>1:
    print(s)
else:
    print(s.title())