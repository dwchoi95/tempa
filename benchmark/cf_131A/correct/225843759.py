# h

h= input()

if h.isupper() or (h[0].islower() and h[1:].isupper()) or (len(h)==1 and h.islower()):
    h= h.swapcase()

print(h)