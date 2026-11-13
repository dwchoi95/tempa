s = input()
s2 = s[1:]
o = False
if s2.isupper() or s2 == '':
    o = True
if o:
    s3 = s[0].upper() + s2.lower()
    print(s3)
else:
    print(s)