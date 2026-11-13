counter = 0

number = input()

for i in range(len(number)):

	if number[i] == '4':

		counter += 1

	elif number[i] == '7':

		counter += 1

if counter == 0:

	print("NO")

else:

	z = 0

	counter = str(counter)

	for i in range(len(counter)):

		if counter[i] != '4':

			if counter[i] != "7":

				z += 1

	if z == 0:

		print("YES")

	else:

		print("NO")