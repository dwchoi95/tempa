string = input()
#string = string[0].upper()
if string[0].islower() and string[1:].isupper():
	string = string[0].upper()+string[1:].lower()
print(string)