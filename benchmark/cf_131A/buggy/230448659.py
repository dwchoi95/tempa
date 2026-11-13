a = input()

import string

if a[0].islower() and a[1:].upper():
    print(a.capitalize())
elif a.upper():
    print(a)
else:
    print(a.capitalize())