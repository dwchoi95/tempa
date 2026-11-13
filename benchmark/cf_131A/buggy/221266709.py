s=input()
c=""
s1=""
if(s.isupper()):
    s1=s.lower()
    print(s1)
if(s[0].islower() and s[1:].isupper()):
    s=s.lower()
    c=s[0].upper()
    s1=c+s[1:]
    print(s1)
if(s[0].isupper() and s[1:].islower()):
    print(s)
if(s[0].islower() and len(s)==1):
    print(s.upper())