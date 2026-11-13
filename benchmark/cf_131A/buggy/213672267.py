a = input()
if a.isupper() or (a[0].islower() and a[1:].isupper()):
    ans = ''
    for i in a:
        if i.islower():
            ans += i.upper()
        else:
            ans += i.lower()
    print(ans)
else:
    print(a)