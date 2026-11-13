n=int(input())
while(n>0):
	if n%10==4 or n%10==7:
		n=n//10
	else:
		break
if n==0:
	print("YES")
else:
	print("NO")