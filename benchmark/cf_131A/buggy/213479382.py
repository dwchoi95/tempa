s=input()
c=s[0]
if c.islower():
    if s[1:].isupper():
        rs=s.swapcase()
        print(rs)
    else:
        print(s)
elif s.isupper():
    es=s.swapcase()
    print(es)
else:
    print(s)