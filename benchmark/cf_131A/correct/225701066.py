s = input()
if (s[0].islower() and s[1:].isupper() or s.isupper() or len(s) == 1 and s.islower()):
    s = s.swapcase()
print(s)