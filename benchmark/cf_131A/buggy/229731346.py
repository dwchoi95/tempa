s=input()
if s[0].islower():
    s1=s[0].upper()
    for i in range(1,len(s)):
        if s[i].islower():
            s1+=s[i].upper()
        else:
            s1+=s[i].lower()
else:
    s1=s 
print(s1)