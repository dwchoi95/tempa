x = input()

if x.isupper():
    print(x.lower())
elif x[0].islower() and all(char.isupper() for char in x[1:]):
    print(x[0].upper() + x[1:].lower())
else:
    print(x)