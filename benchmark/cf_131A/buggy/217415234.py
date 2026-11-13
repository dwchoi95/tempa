a=input()
if a==a.upper() or (a[0]==a[0].upper and a[1:]==a[1:].upper()):
    print(a.swapcase())
else:
    print(a)