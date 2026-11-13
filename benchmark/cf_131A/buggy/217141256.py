x = input()
if x[0].islower():
    if x[1].isupper():
        x = x.lower()
        x = x.capitalize()
        print(x)
        exit(0)
for u in x:
    if u.isupper():
        x = x.lower()
        x = x.capitalize()
        print(x)
        exit(0)
print(x)