from collections import Counter,defaultdict,deque

read = lambda : list(map(int,input().split()))
getinfo = lambda grid: print(list(map(print,grid)))
p = lambda x: print(x,end=" ")

mod = 10**9 + 7
inf = float('inf')

def lastDay(n, day):
	if day == 0: return True
	num = 0
	for val in d.values():
		num += val // day
		if num >= n: return True
	return False

while True:
	try:
		n, m = read()
		a = read()
		d = Counter(a)
		l, r = 0, max(d.values())
		while l < r - 1:
			mid = (l + r) // 2
			if lastDay(n, mid):
				l = mid
			else:
				r = mid

		if lastDay(n, r):
			print(r)
		else:
			print(l)
	except:
		break