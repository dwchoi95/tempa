a=input()
if a.islower():
    print(a)
elif a.isupper():
    print(a.lower())
else:
    print(a[0].upper()+a[1::].lower())