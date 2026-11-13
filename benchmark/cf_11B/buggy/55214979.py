p=int(input())
x=abs(p)
j=int((-1+(1+8*x)**.5)/2)
if (j+j*j)//2==x:
	print(j)
	
else:
	print(j+2 if p>0 else j+3)