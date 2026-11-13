from math import sqrt
x = abs(int(input()))
n = int((sqrt(1 + 8 * x) - 1) / 2)
k = (n * (n + 1)) // 2
if k == x: print(n)
else: print(n + 1 + (n + 1 + k - x) % 2)