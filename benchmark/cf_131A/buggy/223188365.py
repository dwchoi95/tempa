s = input()
if len(s)>=1 or len(s)<= 100:

    if s[0].isupper():
        print(s[0]+s[1:].casefold())
    else:
        if s[1:].isupper():
            print(s[1:].casefold())
        else:
            print(s)