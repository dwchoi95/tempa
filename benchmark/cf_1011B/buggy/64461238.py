n,m=map(int,input().split())
a=list(map(int,input().split()))
b=[]
x=m//n
for i in set(a):
	c=0
	for j in a:
		if(i==j):
			c=c+1
	b.append(c)
sum1=0
if(x==0):
	print(x)
if(len(set(b))==1):
	print('1')
while(sum1!=n and x!=0):
	sum2=0
	for i in b:
		i=i//x
		sum2=sum2+i
		sum1=sum2

	if(sum1==n):
		print(x)
	else:
		x=x-1