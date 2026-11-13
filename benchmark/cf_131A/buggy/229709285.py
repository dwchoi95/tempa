a=input()
if a==a.upper() or a[1::]==a[1::].upper():
    print(a[0].upper()+a[1::].lower())
else:
    print(a)