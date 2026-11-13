n = input()

if len(n) == 1:
    if n.islower():
        n = n.upper()
    else:
        n = n.lower()

elif (n[0].islower() and n[1:].isupper()):
    n = n.capitalize()

elif n.isupper():
    n = n.lower()

print(n)