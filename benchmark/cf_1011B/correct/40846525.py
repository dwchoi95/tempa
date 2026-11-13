#      
import collections, atexit, math, sys
from functools import cmp_to_key
#key=cmp_to_key(lambda x,y: 1 if x not in y else -1 )

sys.setrecursionlimit(1000000)
def getIntList():
    return list(map(int, input().split()))    

import bisect 
try :
    #raise ModuleNotFoundError
    import numpy
    def dprint(*args, **kwargs):
        print(*args, **kwargs, file=sys.stderr)
    dprint('debug mode')
except ModuleNotFoundError:
    def dprint(*args, **kwargs):
        pass


def memo(func):  
    cache={}  
    def wrap(*args):  
        if args not in cache:  
            cache[args]=func(*args)  
        return cache[args]  
    return wrap

@memo
def comb (n,k):
    if k==0: return 1
    if n==k: return 1
    return comb(n-1,k-1) + comb(n-1,k)

inId = 0
outId = 0
if inId>0:
    dprint('use input', inId)
    sys.stdin = open('input'+ str(inId) + '.txt', 'r') #标准输出重定向至文件
if outId>0:
    dprint('use output', outId)
    sys.stdout = open('stdout'+ str(outId) + '.txt', 'w') #标准输出重定向至文件
    atexit.register(lambda :sys.stdout.close())     #idle 中不会执行 atexit
    
N, M = getIntList()
za = getIntList()

zc = [0 for i in range(101)]
for x in za:
    zc[x] +=1

#dprint('zc',zc)

min_ok = 0
max_not = 101

def work(day):
    c = 0
    for i in range(101):
        c += zc[i] // day
    return (c>=N)

while min_ok + 1 < max_not:
    mid = (min_ok + max_not ) //2
    if work(mid) :
        min_ok = mid
    else:
        max_not = mid

print(min_ok)