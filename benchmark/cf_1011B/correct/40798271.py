n,m=map(int,input().split())
a=list(map(int,input().split()))
d={}
for i in a:
	if i in d:
		d[i]+=1
	else:
		d[i]=1
x=[]
for i in d:
	x.append(d[i])
k=m//n
ans=0
while k>0:
	p=0
	e=x[:]
	#print("e=",e)
	for i in range(len(x)):
		while e[i]>=k:
			p+=1
			e[i]-=k
	#print(k,p)
	if p>=n:
		ans=k
		break
	k-=1
	if k<=0:
		break
	#print(x,e)
print(ans)