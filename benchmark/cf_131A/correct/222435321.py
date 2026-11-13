s = input()
if len(s) == 1 and s.islower():
    print(s.upper())
elif s.isupper():
    print(s.swapcase())
elif s[1:].isupper() and s[0].islower():
    print(s.swapcase())
else:
    print(s)