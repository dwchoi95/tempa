s=input()
l=len(s)
n=' '
if s.isupper():
    print(s)
elif s[0].isupper() and s[1:].islower():
    print(s)
else:
    for i in s:
        if i.isupper():
            n+=i.lower()
        else:
            n+=i.upper()
    print(n)