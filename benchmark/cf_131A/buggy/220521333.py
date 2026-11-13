x = input()
if(x.isupper()):
	x = x.lower()
	print(x)
elif(x[1::].isupper()):
	x = x.title()
	print(x)
else:
	print(x)