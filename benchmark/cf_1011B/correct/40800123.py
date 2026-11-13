import math
import itertools
from collections import defaultdict
getInputList = lambda : list(input().split())
getInputIntList = lambda : list(map(int,input().split()))

n , m = getInputIntList()
arr = getInputIntList()
myset = defaultdict(int)
for i in arr:
    myset[i] += 1
l = []
for k,v in myset.items():
    l.append(v)
l.sort(reverse=True)
ans = 0
for i in range(100,0,-1):
    to = 0
    for j in l:
        to += j//i
    if to >= n:
        ans=i
        break
print(ans)