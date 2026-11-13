n=int(input())
c4,c7=0,0
while(n>0):
	if n%10==4 or n%10==7:
		if n%10==4:
			c4=1
		else:
			c7=1
		n=n//10
	else:
		break
if n==0 and c7==1 and c4==1:
	print("YES")
else:
	print("NO")