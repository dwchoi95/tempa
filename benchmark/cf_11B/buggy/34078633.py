target = int(input())
c = 0
while True:
	factor = c * (c + 1) * 0.5

	if factor * -1 <= target <= factor:
		temp = factor - target
		if temp % 2 == 1:
			c += 1
		break

	c += 1

print(c)