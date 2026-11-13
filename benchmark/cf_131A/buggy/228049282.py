n = input()
if n.isupper():
    n = n.capitalize()
    quit()
if n[0].islower() and n[1:].isupper():
    n = list(n)
    for i in range(0, len(n)):
        if n[i].islower():
            n[i] = n[i].upper()
        else:
            n[i] = n[i].lower()
    t = ''
    for i in range(len(n)):
        t += n[i]
    print(t)
    quit()
print(n)