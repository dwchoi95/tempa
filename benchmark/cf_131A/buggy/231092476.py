n=input()
if n[0].islower() and n[1:].isupper() or n.capitalize():
    n=n.capitalize()
print(n)