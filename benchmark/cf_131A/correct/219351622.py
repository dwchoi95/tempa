x = input()
y = x.upper()
if x == y:
        print(x.lower())
elif x[1:] == y[1:]:
        print(x[0].upper() + x[1:].lower())
else:
        print(x)