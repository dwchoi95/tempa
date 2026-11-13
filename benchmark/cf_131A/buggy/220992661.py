n=input()
z=((n[0].upper())+(n[1:].lower()))
if n.islower():
    print(n.upper())
elif (n[0].islower()) and (n[1:].isupper()):
    print(z)
elif n.isupper():
    print(z)
else:
    print(n)