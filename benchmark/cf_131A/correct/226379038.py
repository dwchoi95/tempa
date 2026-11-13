s = input()
if s[1:] == s[1:].upper():
    new_s = ''
    for l in s:
        if l.upper() == l:
            new_s += l.lower()
        else:
            new_s += l.upper()
    print(new_s)
else:
    print(s)