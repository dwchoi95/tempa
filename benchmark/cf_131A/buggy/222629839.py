s = input()

if s.upper() == s:
    print(s.capitalize())
elif s[1:].upper() == s[1:] and s[0].lower() == s[0]:
    print(s.capitalize())
else:
    print(s)