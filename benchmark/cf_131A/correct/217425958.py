a = input()
if a.isupper() or (a[0].islower() and a[1:].isupper()) or (len(a) == 1 and a.islower()):
    a = a.swapcase()
print(a)