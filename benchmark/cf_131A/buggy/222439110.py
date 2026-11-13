n=input()
b=n[0]
c=b
if(n.isupper() or n.islower() or (b.islower() and c.isupper()) ):
    a=n.capitalize()
    print(a)
else:
    print(n)