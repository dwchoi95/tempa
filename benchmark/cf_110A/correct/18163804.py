word = input()

count = 0

for i in word:

	if(i == '4' or i == '7'):

		count += 1

cek = True

if(count <=9):

	if(count == 4 or count == 7):

		cek = True

	else:

		cek = False

while count > 9 and cek:

	if(count%10 == 4 or count%10 == 7):

		count = count // 10

	else:

		cek = False

if(cek):

	print("YES")

else:

	print("NO")