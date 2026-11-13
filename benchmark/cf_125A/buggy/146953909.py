import math

n = int(input())
ft = n / 36
frctn, intzr = math.modf(ft)
fts = int(intzr)
cm = round(frctn * 12)

print(fts, cm)