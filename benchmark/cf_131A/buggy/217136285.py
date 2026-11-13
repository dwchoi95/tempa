a = input()
print(a.capitalize() if a.isupper() or (a[0].islower() and a[1:].isupper()) else a)