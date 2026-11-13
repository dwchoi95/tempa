from collections import defaultdict

def works(k,n,qty):
	
	if k==0 :
		return True
	
	maxppl=0
	for key in qty.keys() :
		maxppl += qty[key]//k
		
	return maxppl>=n	
	
def solve(n,m,arr):
	# print the max num of days the exped can last.
	
	qty = defaultdict(int)
	
	maxdays = -float('inf')
	for x in arr :
		qty[x]+=1
		maxdays = max(maxdays,qty[x])
		
	# n ppl are there.
	
	# I think we can do bin search on k
	# k can at max be max freq, min will be 0. 
	# True True True True True False False False.
	# Find the last True.
		
	l,r = 0,maxdays
		
	while(l<r):
		
		k = (l+r+1)//2
		
		# True	
		if works(k,n,qty) :	
			l=k
		else :
			r=k-1	
		
	print(l)	
	
n,m = map(int,input().split())
arr= list(map(int,list(input().split())))
solve(n,m,arr)