s=input()
if s[0].islower():
    f=True
    for i in s[1:]:
        if i.islower():
            f=False
    if f==False:
        print(s)
    else:
        print(s[0].upper() + s[1:].lower())
else:
    f=True
    for i in s[1:]:
        if i.islower():
            f=False
    if f==False:
        print(s)
    else:
        print(s.lower())