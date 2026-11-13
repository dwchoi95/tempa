s = input()
if len(s) == 1:
    s = s.swapcase()
else:
    if s[0].islower() and s[1:].isupper():
        s = s.swapcase()
    if s.isupper():
        s = s.lower()
print(s)