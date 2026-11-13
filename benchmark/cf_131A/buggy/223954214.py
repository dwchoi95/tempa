s = str(input())
x = s.upper()
z = s[0].lower() + s[1:].upper()
r = ""
if len(s) == 1:
    r = s[0].lower()
if s == x or s == z or s == r:
    z2 =  s[0].upper() + s[1:].lower()
    print(z2)
else:
    print(s)