a=input()
if a==a.upper():
    print(a.lower())
elif a==a[0].lower()+a[1:].upper():
    print(a[0].upper()+a[1:].lower())
else:
    print(a)