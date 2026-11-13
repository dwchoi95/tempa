b = input()

if b.isupper():
    print(b.lower())
elif b[1:].isupper():
    print(b[0] + b[1:].lower())
else:
    print(b)