w = input()
if w.isupper() or w.swapcase().istitle():
    print(w.swapcase())
else:
    print(w)