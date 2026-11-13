a = input()

if a[1:].isupper() or (len(a) == 1 and a.islower()):
    print(a.capitalize())
elif a.isupper():
    print(a.lower())
else:
    print(a)