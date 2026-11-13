n,m=map(int,input().split())
a=list(map(int,input().split()))
freq=[0]*101
for i in range(m):
	freq[a[i]]+=1

maxx = max(freq)
maximi = 0
# print(maxx)
for i in range(maxx,0,-1):
	cou = 0
	for x in range(101):
		if(freq[x] >= i):
			pp = freq[x]
			cou += pp//i
	if(cou >= n):
		maximi = max(maximi,i)

print(maximi)