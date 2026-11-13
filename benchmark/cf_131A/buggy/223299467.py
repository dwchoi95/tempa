s = input()
if (s[0].swapcase() == s[0].upper() and s[1:].swapcase() == s.lower()) or s.swapcase() == s.lower():
    s= s.capitalize()
print(s)