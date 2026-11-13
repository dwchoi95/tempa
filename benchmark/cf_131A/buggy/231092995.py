n=input()
if (n[0].islower() and n[1:].isupper()):
    n=n.capitalize()
elif n.isupper():
    n=n.lower()
print(n)