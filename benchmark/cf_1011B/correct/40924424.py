n,m = map(int,input().split())

a = list(map(int,input().split()))
dic = dict()
for i in range(m):
	if(a[i] not in dic):
		dic[a[i]] = 1
	else:
		dic[a[i]] +=1

b = 1
while sum(dic[i]//b for i in dic) >= n:
	b +=1
print(b-1)