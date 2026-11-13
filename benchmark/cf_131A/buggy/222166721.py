import math
#f = open("test.txt")

txt = input()
lst = list(txt)

for i in range(len(lst)):
	if (i == 0 and lst[i] == lst[i].lower()):
		lst[i] = lst[i].upper()
	elif (i > 0 and lst[i] == lst[i].upper()):
		lst[i] = lst[i].lower()

print("".join(lst))