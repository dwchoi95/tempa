a=str(input())
if len(a)==1:
    print(a.lower())
else:
    if a[1:]==a[1:].upper():
        print(a.capitalize())
    else:print(a)