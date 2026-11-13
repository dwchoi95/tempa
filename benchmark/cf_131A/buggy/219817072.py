s = input()
if s.isupper() or (s[1:].isupper() and s[0].islower()):
    print(s.swapcase())
else:
    print(s)