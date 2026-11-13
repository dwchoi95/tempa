x = input()
if x.isupper() or (x[0].isupper() and x[1:].islower() ):
	print(x)
else:
	print(x[0].upper()+x[1:].lower())