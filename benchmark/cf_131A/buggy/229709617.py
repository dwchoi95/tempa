a=input()
if a[1::]==a[1::].upper():
    print(a[0].upper()+a[1::].lower())
elif a==a.upper():
    print(a.lower())
else:
    print(a)