s = input(); e = ""; l = len(s)
if l == 1:
    print(s.upper() if s.islower() else s.lower())
elif (s[0].islower() and s[1:].isupper()) or s.isupper():
    for i in range(l):
        e += s[i].lower() if s[i].isupper() else s[i].upper()
    print(e)
else:
    print(s)