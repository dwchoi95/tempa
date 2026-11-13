x=int(input())
x=abs(x)
j=int((-1+(1+8*x)**.5)/2)
if (j+j*j)//2==x:
	print(j)
else:
	print(j+2)