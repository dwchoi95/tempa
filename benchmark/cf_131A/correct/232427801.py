s  = input()
c = True
for i in range (1, len(s)):
    if s[i].islower():
        c = False
if c:
    for j in range(len(s)):
        if s[j].islower():
            u = s[j].upper()
        else:
            u = s[j].lower()
        print(u, end="")
else:
    print(s)