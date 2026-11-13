def d(n):
	while len(str(n))!=1:
		n = sum(int(d) for d in str(n))
	return n

print(d(input()))