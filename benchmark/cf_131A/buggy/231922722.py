a = input()
if a[0].islower() or a[1:].isupper():
    print(a.swapcase())
else:
    print(a)