x = input()
if (len(x) == 1 and x.islower()) or (x[0].islower() and x[1:].isupper()):
    print(x.capitalize())
    exit()
if x.islower():
    x = x.upper()
if x.isupper():
    x = x.lower()


print(x)