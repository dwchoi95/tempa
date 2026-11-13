a = input().split(" ")
n , m = int(a[0]) , int(a[1])

a = input().split(" ")
a = [int(x) for x in a]

food = {}
for x in a:
	if(food.get(x)==None):
		food[x] = 1
	else:
		food[x]+= 1
print(food)
max_days = 0
for x in range(n,0,-1):
	chk = 0
	for y in food.values():
		chk+=y//x
	if(chk>=n):
		max_days = x
		break
print(max_days)