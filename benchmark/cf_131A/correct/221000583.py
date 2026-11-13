x = input()
if x.isupper():
	print(x.lower())
elif x[0].islower() and x[1:].isupper():
	print(x[0].upper()+x[1:].lower())
elif x[0].isupper() and x[1:].islower():
	print(x[0].upper()+x[1:].lower())
elif (len(x) == 1) and x.lower():
	print(x.upper())
else:
	print(x)