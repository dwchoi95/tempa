a = input()
if a.isupper():
    a = a.lower()
elif a[0].islower() and a[1:].isupper():
    a = a[0].upper() + a[1:].lower()
elif a.islower() and len(a)==1:
    a = a.upper()
else:
    a = a
print(a)