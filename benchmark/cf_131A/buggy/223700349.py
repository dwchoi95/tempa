a=input()
b=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
c=['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
d=''
flag=True
if len(a)>1:
    for j in a[1:]:
        if j not in c:
            flag=False
if a[0] in b and len(a)>1 and flag:
    for i in a:
        if i in b:
            d+=c[b.index(i)]
        else:
            d+=b[c.index(i)]
    print(d)
else:
    print(a)