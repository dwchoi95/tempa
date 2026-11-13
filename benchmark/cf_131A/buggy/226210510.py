w = str(input())
if w.isupper() or (w[0].islower() and w[1:].isupper()):q = w.swapcase();print(q)
else:print(w)