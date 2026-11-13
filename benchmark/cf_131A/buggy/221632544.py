w = input()
if w.isupper() or (w[0].islower() and w[1:].isupper()):
    print(w.swapcase())
else:
    print(w)