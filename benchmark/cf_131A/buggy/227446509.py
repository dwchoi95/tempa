w = input()

if (len(w) == 1) and (w[-1].islower()):
    print(w.isupper())
elif w.isupper():
    print(w.lower())
elif w[0].islower() and w[1:].isupper():
    print(w[0].upper()+ w[1:].lower())
else:
    print(w)