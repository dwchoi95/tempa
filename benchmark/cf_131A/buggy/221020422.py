a = input()
if a.isupper():
    a = a[0] + a[1:].lower()
elif a[0].islower() and a[1:].isupper():
    a = a[0].upper() + a[1:].lower()
else:
    a = a[0].upper() + a[1:]
print(a)