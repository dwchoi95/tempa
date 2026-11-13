a = input()
print(a.swapcase() if a[1:].isupper() or a[0].islower() else a)