n, m = map(int, input().split())
a = list(map(int, input().split()))
d = dict()
for i in a:
	if i not in d:
		d[i] = 1
	else:
		d[i] += 1
x = []
for j in d:
	x.append(d[j])
x.sort(reverse = True)
def f(t):
	ans = 0
	for i in x:
		ans += i // t
	if ans >= n:
		return True
	return False
left = 0
right = 10 ** 9
while (left + 1 != right):
	mid = (left + right) // 2
	if f(mid):
		left = mid
	else:
		right = mid
print(left)
#print(f(2))