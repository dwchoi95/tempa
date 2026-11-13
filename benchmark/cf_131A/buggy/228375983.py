a=input()
o=0
for x in range(1,len(a)):
    if a[x]==a[x].lower():
        o+=1
if o>0:
    print(a)
else:
    b=a.lower()
    b=b[0].upper()+b[1:]
    print(b)