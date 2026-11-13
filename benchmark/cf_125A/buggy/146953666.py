import math

n = int(input())

ft = n / 36
frctn, intzr = math.modf(ft)
ft = int(intzr)
cm = round(frctn * 12)

print(ft, cm)