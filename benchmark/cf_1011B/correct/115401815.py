# Problem: B. Planning The Expedition
# Contest: Codeforces - Codeforces Round #499 (Div. 2)
# URL: https://codeforces.com/contest/1011/problem/B
# Memory Limit: 256 MB
# Time Limit: 1000 ms
# Powered by CP Editor (https://github.com/cpeditor/cpeditor)

from sys import stdin
def get_ints(): return list(map(int, stdin.readline().strip().split()))

n,m = get_ints()
ar = get_ints()
counts  =[0]*105
for num in ar:
	counts[num]+=1
	
ans = 0
for i in range(1,m+1):
	cnt = 0
	for j in range(1,101):
		cnt+=counts[j]//i;
	if cnt>=n:
		ans = max(ans,i) 
print(ans)