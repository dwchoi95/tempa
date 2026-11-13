s = input()
if s.isupper() or (len(s) > 1 and s[1:].islower()):
    s = s.swapcase()
print(s)