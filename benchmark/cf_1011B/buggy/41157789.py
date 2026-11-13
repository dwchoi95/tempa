a = input()
l = list(map(int,a.split()))
n = l[0]
m = l[1]

b = input()
r = list(map(int,b.split()))

x = []

for i in range(0,102):
	x.append(0)

for i in r :
	x[i]=x[i]+1

nx = sorted(x)

vis = 0
ans = 0

for i in range(100,-1,-1):
	bum = (i*n)
	if(vis) :
		break	
	for j in range(0,len(nx)) :
		if(vis) :
			break
		bum= bum - nx[j]
		if(bum<=0):
			if(nx[j]>=i):
				vis=1
				ans= i

print(ans)