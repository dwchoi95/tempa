n = input()
if n.isupper():
    print(n.capitalize())
else:
    if n[0].isupper() == False:
        print(n.capitalize())
    else:
        print(n)