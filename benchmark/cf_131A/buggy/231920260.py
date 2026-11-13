x = input()
if x.isupper():
    x = x.lower()
if x[0].islower() and x[1:].isupper():
    x = x.capitalize()
print(x)