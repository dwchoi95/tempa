import bisect
import os
from collections import Counter
import bisect
from collections import defaultdict
import math
import random
import heapq as hq
from math import sqrt
import sys
from functools import reduce, cmp_to_key
from collections import deque
import threading
from itertools import combinations
from io import BytesIO, IOBase
from itertools import accumulate

# sys.setrecursionlimit(200000)
# mod = 10**9+7

def sort_dict(key_value):
    return sorted(key_value.items(), key = lambda kv:(kv[1], kv[0]))

def list_input():
    return list(map(int,input().split()))
    
def num_input():
    return map(int,input().split())
    
def string_list():
    return list(input())
        
n,m = num_input()
arr = list_input()

if n > m:
    print(0)
else:
    N = n
    count = {}
    for i in arr:
        try:
            count[i] += 1
        except KeyError:
            count[i] = 1
            
    count = sort_dict(count)
    i = len(count)-1
    summ = 0
    while n > 0 and i >= 0:
        (f,c) = count[i]
        summ += c
        i -= 1
        n -= 1
    print(summ//N)