s = input()
if s.isupper() or s[0].islower():
    if len(s) == 1 and s.islower():
        print(s.swapcase())
    if len(s) > 1 and s[1].isupper() and s[0].islower():
        print(s.swapcase())
else:
    print(s)