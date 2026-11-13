w = input()
if w[0].isupper() or w[0].islower() and w[1::].isupper():
    print(w.capitalize())
else:
    print(w)