n = input()

if n.isupper():
    print(n.capitalize())
elif n[1:].isupper():
    print(n.capitalize())
else:
    print(n)