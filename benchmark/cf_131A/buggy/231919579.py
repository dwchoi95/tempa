x = input()
if ("capslock" not in x.lower()):
    print(x.capitalize())
else:
    print(x[0].lower() + x[1:].upper())