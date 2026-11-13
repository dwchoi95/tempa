word = input()

h = 0

if len(word) == 1:

	print(word.swapcase())

else:

	for i in range(len(word)-1):

		temp = word[i+1]

		if temp.islower() == 1:

			print(word)

			h = -1

			break

	if h == 0:

		print(word.swapcase())