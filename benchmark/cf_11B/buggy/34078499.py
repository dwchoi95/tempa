def abs(val):
	if val < 0:
		return val * -1
	return val

target = int(input())

x = 0
step = 1

while x != target:
	if abs(target - x) >= step:
		if target - x > 0:
			x += step
		else:
			x += step * -1

		step += 1

	else:
		if target - x > 0:
			x += step * -1
		else:
			x += step

		step += 1

print(step - 1)