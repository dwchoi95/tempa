s = str(input())
l = len(s)
if l is 1:
    if s.islower():
        print(s.upper())
    else:
        print(s.lower())
elif s[1:l].isupper():
    if s[0].isupper():
        print(s.lower())
    else:
        s = s.lower()
        print(s[0].upper() + s[1:l])
else:
    print(s)