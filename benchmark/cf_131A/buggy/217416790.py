a = input()
if a.islower() or (a[0].islower and a[1:].isupper) or a.isupper or (a[0].isupper and a[1:].islower):
    a = a.swapcase()
    print(a)
else:
    print(a)