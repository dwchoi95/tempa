s = input()
def flip(s):
    return (s[0].upper() if s[0].islower() else s.lower()) + s[1:].lower()
res = flip(s) if all(c.isupper() for c in s[1:]) else s
print(res)