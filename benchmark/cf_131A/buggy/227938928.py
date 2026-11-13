s = input()
if s.isupper():
    print(s.lower())
else:
    if s[1:].isupper():
        print(s[0].upper()+s[1:0].lower())
    else:
        print(s)