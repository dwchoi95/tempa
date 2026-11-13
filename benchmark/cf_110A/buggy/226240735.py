n=int(input())
a=str(n)
flag=True
for i in range(len(a)):
	if a[i] in '01235689':
		flag=False
if flag==True:
	print('YES')
else:
	print('NO')