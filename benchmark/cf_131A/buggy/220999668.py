x = input()
if x[1:].isupper():
	print(x[0].upper()+x[1:].lower())
elif x[0].isupper() and x[1:].islower():
	print(x[0].upper()+x[1:].lower())
else:
	print(x)