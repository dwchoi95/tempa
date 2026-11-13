from math import sqrt, floor

n = int(input())

true_products, a = 0, 1

while a ** 2 <= n:
	true_products += n // a - a
	a += 1

true_products *= 2

true_products += floor(sqrt(n))

digit_roots = [n // 9 for _ in range(9)]
for i in range(1, n % 9 + 1):
	digit_roots[i] += 1

digit_root_products = 0

for i in range(9):
	for j in range(9):
		digit_root_products += digit_roots[i] * digit_roots[j] * digit_roots[(i * j) % 9]

print(digit_root_products - true_products)