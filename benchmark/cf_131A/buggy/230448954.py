a = input()

import string
if len(a) == 1:
    print(a.upper())
elif a.islower():
    print(a.lower())
elif a[0].islower() and a[1:].upper():
    print(a.capitalize())
elif a.upper():
    print(a)
else:
    print(a.capitalize())