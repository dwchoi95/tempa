import collections
n,l=map(int, input().split())
array = list(map(int, input().split()))
c=collections.Counter(array).values()
cur=1
while sum(x//cur for x in c)>=n:cur+=1
print(cur-1)