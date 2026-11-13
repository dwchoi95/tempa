x = input()
if(x[1::].isupper()):
	x = x.title()
	print(x)
elif(x.isupper()):
	x = x.title()
	print(x)
else:
	print(x)