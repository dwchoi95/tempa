a = input()
if a[1:].isupper() or (len(a) == 1 and a.islower()):
    a = a.swapcase()
print(a)