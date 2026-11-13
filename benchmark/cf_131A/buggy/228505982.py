s=input()
a=s[0]+s[1:].upper()
if s==s.lower() or s==s.capitalize():
    print(s)
elif s==a or s==s.upper():
    print(s.capitalize())
else:
    print(s)