l = input()


if l.isupper():
    print(l.lower())

elif l[1:].isupper():
    print(l.swapcase())
else:
    print(l)