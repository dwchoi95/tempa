s = input()
first_char = s[0]

if s.isupper():
    print(s.lower())
elif first_char.islower() and s[1:].isupper():
    print(first_char.upper() + s[1:].lower())
else:
    print(s)