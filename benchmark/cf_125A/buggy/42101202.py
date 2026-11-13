n = int(input())
add = (n%36)%3
if add >= 2:
	add = 1
else:
	add = 0
print(n//36, (n%36)//3+add)