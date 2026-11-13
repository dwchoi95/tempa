def main():
	x = int(input())
	print(jumps(x))

def jumps(n):
	i = 0
	while True:
		product = i * (i + 1) // 2
		if product >= n and product % 2 == n % 2:
			return i
		i += 1

#print(jumps(6))
main()