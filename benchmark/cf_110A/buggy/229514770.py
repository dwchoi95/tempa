s = str(int(input()))

c=0
for i in s:
	if i == '4' or i == '7':
		c += 1


print(c == len(s))