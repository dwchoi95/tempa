s=input()
if(s[0]!=s[0].upper() and s[1:]==s[1:].upper()):
    print(s[0].upper()+s[1:].lower())
if(s==s.upper()):
    print(s.lower())
else:
    print(s)