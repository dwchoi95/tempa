n = int(input())

a = n//36
b = 0
if n%36 >= 18:
	a+=1
	n = 0
else:
	b = (n%36)//3
	if (n%36)%3 >= 2:
		b+=1

print(a, b)