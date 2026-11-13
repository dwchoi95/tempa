a = input()

if len(a) == 1 and a.islower():
    print(a.capitalize())
elif a[1:].isupper() or a.isupper():
    print(a.swapcase())
else:
    print(a)