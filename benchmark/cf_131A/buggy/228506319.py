s=input()
a=s[0]+s[1:].upper()
if len(s)==1:
    print(s.upper())
elif s==s.lower() or s==s.capitalize() and len(s)>1:
    print(s)
elif s==s.upper():
    print(s.lower())
elif s==a:
    print(s.capitalize())
else:
    print(s)