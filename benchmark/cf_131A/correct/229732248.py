s=input()
if s[0].islower() and s[1::].isupper():
    s1=s[0].upper()
    for i in range(1,len(s)):
        if s[i].islower():
            s1+=s[i].upper()
        else:
            s1+=s[i].lower()
elif len(s)==1:
    if s.isupper():
        s1=s.lower()
    else:
        s1=s.upper()
elif s.isupper():
    s1=s.lower()
else:
    s1=s 
print(s1)