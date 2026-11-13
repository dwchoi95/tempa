s = input()
if (s[0].islower() and s[1:].isupper() or s.isupper()):
    s = s.swapcase()
print(s)