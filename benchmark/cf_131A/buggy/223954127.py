s = str(input())
x = s.upper()
z = s[0].lower() + s[1:].upper()

if s == x or s == z:
    z2 =  s[0].upper() + s[1:].lower()
    print(z2)
else:
    print(s)