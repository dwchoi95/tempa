from collections import defaultdict, deque, Counter
from functools import lru_cache
from heapq import heappush, heappop
from bisect import bisect_right, bisect_left

def inpNum():
    return int(input())
def inpStr():
    return input()
def inpSepNum():
    return map(int, input().split())
def inpNumList():
    return list(map(int, input().split()))
def inpChList():
    return list(input().split())
m, n = inpSepNum()
nums = inpNumList()
freq = Counter(nums)
trial = n // m
while trial:
    cur = m
    for k, v in freq.items():
        cur -= v // trial
        if cur == 0:
            print(trial)
            exit(0)
    trial -= 1
print(0)