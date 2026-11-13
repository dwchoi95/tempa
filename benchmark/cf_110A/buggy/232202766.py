string = input()
string_length = len(string)
 
if (string_length == string.count("4") + string.count("7")):
	print("YES")
else:
	print("NO")