f = input()
if f[0] == f[0].lower() and f[1:] == f[1:].upper():
    print(f[0].upper() + f[1:].lower())
else:
    print(f)