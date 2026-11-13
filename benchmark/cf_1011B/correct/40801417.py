from collections import Counter

k,n=list(map(int,input().split()))
a=list(map(int,input().split()))
a=dict(Counter(a))
a=sorted(list(a.values()),reverse=True)

i=a[0]
while i>=1:
	count=0
	for j in range(len(a)):
		count+=a[j]//i
	if count>=k:
		break
	i-=1

if i==0:
	print(0)
else:
	print(i)