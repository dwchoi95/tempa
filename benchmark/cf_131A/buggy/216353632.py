s=input()
c=0
flag=True
for i in range(len(s)):
    if s[i].lower() == s[i]:
        c+=1
    if s[i].lower() == s[i] and i!=0:
        flag=False
if c<1:
    print(s.title())
elif c>1:
    print(s)
else:
    if flag:
        print(s.title())
    else:
        print(s)