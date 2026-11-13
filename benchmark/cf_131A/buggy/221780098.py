s = input()

if len(s) == 1:
    if s == s.lower():
        print(s.upper())
    else:
        print(s)    
else:
    if s[0] == s[0].lower() and s[1:] == s[1:].upper():
        ns = s[0].upper() + s[1:].lower()
        print(ns)
    elif s == s.upper():
        print(s.lower())
    else:
        print(s)