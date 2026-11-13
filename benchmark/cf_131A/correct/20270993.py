s=input()

z=len(s)

if z==1:

	if s.islower():

		print(s.upper())

	else:

		print(s.lower())

else:

	if s[0:].isupper():

		print(s.lower())

	elif s[1:].isupper():

		print(s.capitalize())

	else:

		print (s)