n = int(input())
a = n // 36
b = (n - a * 36) // 3
n = n - 36 * a - 3 * b
b += (n == 2)
if b == 12:
  a, b = a + 1, 0
print(a, b)