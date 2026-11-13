s = input()
s2 = s[1:]
if s.isupper():
    print(s.lower())
elif s2.isupper() or len(s) == 1:
    print(s[0].upper() + s2.lower())
else:
    print(s)