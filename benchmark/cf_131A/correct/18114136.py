word = input()

wordupper = word.upper()

if(word == wordupper or (word[1:] == wordupper[1:] and word[0] == word[0].lower())):

	#print ('change')

	print(word.swapcase())

else:

	print (word)