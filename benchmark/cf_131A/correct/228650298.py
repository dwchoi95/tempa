string = input()

def invert(s):
    if s.isupper():
        return s.lower()
    return s.upper()

if len(string) == 1 or string[1:].isupper():
    print(invert(string[0]) + string[1:].lower())
else:
    print(string)