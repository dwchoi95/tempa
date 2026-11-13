import sys
import math
from collections import OrderedDict
def input():    return sys.stdin.readline().strip()
def iinput():   return int(input())
def minput():   return map(int, input().split()) 
def listinput(): return list(map(int, input().split()))
n,m = minput()
a=listinput()
s=0
if m<n:print(0)
elif len(list(dict.fromkeys(a)))==m:print(1)
else:
	while len(a)>0:
		s+=a.count(a[0])
		a = list(filter((a[0]).__ne__, a))
	print(s//n)