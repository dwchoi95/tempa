target = int(input())

c = 0

while True:
	factor = c * (c + 1) * 0.5

	if factor * -1 <= target <= factor:
		break

	c += 1

print(c)