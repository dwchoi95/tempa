s = input()
first_char = s[0]
if s.isupper():
    print(s.lower())
if first_char.islower():
    print(s.capitalize())
if s.istitle():
    print(s)