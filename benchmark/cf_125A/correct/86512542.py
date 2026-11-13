def solve():
	n = int(input())
	remainder = n % 3
	if remainder > 1:
		n += 1
	elif remainder == 1:
		n -= 1

	print(n // 36, (n - n // 36 * 36) // 3)

solve()