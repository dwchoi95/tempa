import math
n=int(input())
b=round(n/3)
a=math.floor(b/12)
b=b-a*12
print(a,b)