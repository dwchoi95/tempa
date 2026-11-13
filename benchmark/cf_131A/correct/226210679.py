w = str(input())
if len(w) < 2 : t = w.swapcase();print(t)
elif w.isupper() or (w[0].islower() and w[1:].isupper()):q = w.swapcase();print(q)
else:print(w)