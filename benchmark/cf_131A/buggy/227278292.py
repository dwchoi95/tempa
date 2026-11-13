a = input()
if a[0].islower() and a[1:].isupper() or a.islower() or a.isupper():
	print(a[0].upper() + a[1:].lower())
else:
	print(a)