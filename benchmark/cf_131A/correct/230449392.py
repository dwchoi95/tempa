a = input()

if len(a)>1:

    if a.upper() == a:

        print(a.lower())
    elif a[1:].upper() == a[1:]:

        print(a.capitalize())
    else:
        print(a)
else:
    print(a.swapcase())