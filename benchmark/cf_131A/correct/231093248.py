n=input()
if (n[0].islower() and n[1:].isupper()):
    n=n.capitalize()
elif n.isupper():
    n=n.lower()
elif n.islower() and len(n)==1:
    n=n.upper()
print(n)