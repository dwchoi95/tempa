a=str(input())
c=0
for i in a:
	if i =="4" or i=="7":
		c+=1
if "4" in a and "7" in a:
	if c==len(a):
		print("YES")
	else:
		print("NO")
else:
	print("NO")