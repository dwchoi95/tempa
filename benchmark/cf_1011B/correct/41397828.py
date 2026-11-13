n,m = map(int,input().split())
a = list(map(int,input().split()))
d = {}
for i in a:
	try:
		d[i]
	except:
		d[i]=1
	else:
		d[i]+=1
l = list(d.values())
l.sort()
md=0
for i in range(m,0,-1):
	a = l[:]
	for j in range(len(a)):
		a[j] = a[j]//i
	if sum(a)>=n:
		md=i
		break
print(md)