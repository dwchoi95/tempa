a = input()
b = a.upper()
if a == b:
    print(a[0]+a[1:len(a)].lower())
elif a == a[0]+b[1:len(a)]:
    print(a[0].upper()+a[1:len(a)].lower())
else:
    print(a)