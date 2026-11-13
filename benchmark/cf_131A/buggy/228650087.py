string = input()

def Invert(s):
    if s.isupper():
        return s.lower()
    return s.upper()

if string[1:].isupper():
    print(Invert(string[0]) + string[1:].lower())
else:
    print(string)