s = str(input())
x = s.upper()
z = s[0].lower() + s[1:].upper()
r = ""
if len(s) == 1:
    r = s[0].lower()
if s == x or s == z or s == r:
    a = list()
    for k in range(len(s)):
        if s[k].isupper():
            a.append(s[k].lower())
        else:
            a.append(s[k].upper())
    print("".join(a))
else:
    print(s)