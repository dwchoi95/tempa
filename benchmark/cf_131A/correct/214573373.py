s = input()
if len(s) == 1 or s[1:].upper() == s[1:]:
    s = s.swapcase()
print(s)