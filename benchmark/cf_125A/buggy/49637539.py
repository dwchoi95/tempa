from math import ceil
a = int(input())
f = str(a//36)
d = ceil(a%36/3)
if d == 12:
	f+=1
print(f+' '+str(d))