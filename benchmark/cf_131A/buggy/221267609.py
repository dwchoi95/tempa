a = input()
a2 = ""
if a.isupper() == True:
    a2 += a.lower()
elif a[0].islower() and a[1:].isupper():
    a2 += a[0].upper()
    a2 += a[1:].lower()
else:
    a2 += a

print(a2)