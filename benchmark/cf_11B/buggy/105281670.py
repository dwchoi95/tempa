import math
n = int(input())
x1 = math.ceil(abs((1 + math.sqrt(1 + 8*n)) / 2))
x2 = math.ceil(abs((1 - math.sqrt(1 + 8*n)) / 2))
if x1 > x2:
    print(int(x2))
else:
    print(int(x1))