import math

n = int(input())
ft = n / 36
frctn, intzr = math.modf(ft)
ftss = int(intzr)
cm = round(frctn * 12)

print(ftss, cm)