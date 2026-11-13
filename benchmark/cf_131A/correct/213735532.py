s=input()
if len(s)==1:
    if s.islower():
        a=s.upper()
    if s.isupper():
        a=s.lower()
    print(a)
elif s.isupper():
    a=s.lower()
    print(a)
elif s[0].islower() and s[1:].isupper():
    a=s[1:].lower()
    b=s[0].upper()
    print(b+a)
else:
    print(s)