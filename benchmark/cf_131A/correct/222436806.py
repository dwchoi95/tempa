s=input()
k=s.upper()
if s==k:
     k=s.lower()
     print(k)
elif len(s)==1:
     if s==s.lower():
          print(s.upper())
elif s[0]==s[0].lower() and s[1:]==s[1:].upper():
     print(s[0].upper()+s[1:].lower())
else:
     print(s)