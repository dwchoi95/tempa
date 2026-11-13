s = input()
s2 = s[1:]
o = False
if s.isupper():
    print(s[0].lower() + s[1:].lower())
elif s2.isupper():
    print(s[0].upper() + s[1:].lower())
else:
    print(s)