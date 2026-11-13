a = input()
if a.isupper() or a[1:].isupper():
    a = a.swapcase()
print(a)