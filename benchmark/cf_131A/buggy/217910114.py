s = input()
if len(s)>1:
    s= s[0].upper() + s[1:].lower()
else:
    s = s.upper()
print(s)