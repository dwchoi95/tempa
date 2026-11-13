w = input()

if w.isupper():
    print(w[0]+ w[1:].lower())
elif w[0].islower() and w[1:].isupper():
    print(w[0].upper()+ w[1:].lower())
else:
    print(w)