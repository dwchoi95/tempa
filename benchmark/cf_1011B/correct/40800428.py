n,m = map(int,input().split())
arr = list(map(int,input().split()))
val = [0]*101
for num in arr:
	val[num]+=1
val.sort()
pos = 0

for i in range(len(val)):
	if val[i] > 0:
		val = val[i:]
		pos = i
		break
v1 = val[-1]
for i in range(v1):
	flag = 0
	t = -1
	new1 = val.copy()
	for j in range(n):
	
		while (-1*t <= len(new1)) and (new1[t] < (v1-i)):
			t = t - 1

		if -1*t > len(new1):
			flag =1 
			break
		new1[t] -= (v1 - i)

	if flag == 0:
	
		print(v1 -i)
		break
	if i == v1 -  1:
		print(0)