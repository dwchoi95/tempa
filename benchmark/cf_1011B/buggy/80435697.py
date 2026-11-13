from collections import Counter
def PlanExp(n, m, l):
	d = dict(Counter(l))
	curResult = 0
	for i in range(1,100):
		for val in d.values():
			curResult += val//i
		if curResult<n:
			break
		curResult=0
	return i-1

n, m  = map(int, input().split())
#n = int(input())
#m = int(input())
l = list(map(int, input().split()))
result = PlanExp(n, m, l)
print(result)