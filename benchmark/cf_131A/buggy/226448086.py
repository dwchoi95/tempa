s = input()
c = 0
for i in s:
    if i.isupper():
        c += 1
if c == len(s) or c == len(s) - 1:
    r = list(s.lower())
    r[0] = r[0].upper()
    t = "".join(r)
    print(t)
else:
    print(s)