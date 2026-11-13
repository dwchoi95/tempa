x = input()
if x.isupper() or (x[0].islower() and x[1:].isupper()):
    x.capitalize()
print(x)