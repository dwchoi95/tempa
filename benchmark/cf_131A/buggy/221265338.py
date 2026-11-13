s=input()
c=""

if(s.isupper()):
    print(s.lower())
if(s[0].islower() and s[1:].isupper()):
    s=s.lower()
    c=s[0].upper()
    s=c+s[1:]
    print(s)
if(s[0].islower() and s[1:].islower()):
    print(s)
if(s[0].islower() and len(s)==1):
    print(s.upper())