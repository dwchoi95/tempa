num = input()

cou = 0

answ = 'YES'



for i in num:

	if i == '4' or i == '7':

		cou += 1



for i in str(cou):

	if i == '4' or i == '7':

		continue

	else:

		answ = 'NO'

		break

print(answ)