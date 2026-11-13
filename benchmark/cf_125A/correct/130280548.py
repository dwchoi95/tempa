n = int(input())
a = n // 3
b = 0
if n % 3 == 2:
    a += 1
if a >= 12:
    b = a // 12
    a = a % 12
print(b, a)