from math import ceil
n = int(input())
print(str(n//36)+' '+str(ceil((n%36)/3)))