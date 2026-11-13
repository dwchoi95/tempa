s=input()
sum=0
for i in s:
	if(i=="4" or i=="7"):
		sum+=1
if(sum==4 or sum==7):
	print("YES")
else:
	print("NO")