n=input()
if n[0].islower() and n[1:].isupper() or n.isupper():
    n=n.capitalize()
print(n)