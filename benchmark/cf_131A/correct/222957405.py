s = input()
if len(s) == 1 and s.islower() is True:
    print(s.upper())
elif s[0].islower() is True and s[1:].isupper() is True:
    print(s.title())
elif s.isupper() is True:
    print(s.lower())
else:
    print(s)