n = input()
if n[0] == n[0].lower() and n[1:] == n[1:].upper():
    print(n[0].upper()+n[1:].lower())
elif n == n.upper():
    print(n.lower())
else:
    print(n)