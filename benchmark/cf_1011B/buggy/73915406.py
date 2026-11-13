n,m=map(int,input().split())
a=list(map(int,input().split()))
if(m<n):
	print(0)
elif(m==n):
	print(1)
else:
	s=list(set(a))
	o=[]
	if(len(s)==len(a)):
		print(1)
	elif(len(s)==1):
		print(m//n)
	else:
		for i in range(len(s)):
			o.append(a.count(s[i]))
		print(sum(o)//n)