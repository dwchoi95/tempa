import sys
import math
import bisect
import heapq
import itertools
from sys import stdin,stdout
from math import gcd,floor,sqrt,log
from collections import defaultdict, Counter, deque
from bisect import bisect_left,bisect_right, insort_left, insort_right
import re

mod=1000000007

def get_ints(): return map(int, sys.stdin.readline().strip().split())
def get_list(): return list(map(int, sys.stdin.readline().strip().split()))
def get_string(): return sys.stdin.readline().strip()
def get_int(): return int(sys.stdin.readline().strip())
def get_list_strings(): return list(map(str, sys.stdin.readline().strip().split()))

def solve():
    n = get_string()
    lucky = 0

    for i in range(len(n)):
        if n[i] == "7" or n[i] == "4":
            lucky += 1
    
    if lucky == 7 or lucky == 4:
        return "YES"
    return "NO"
    

if __name__ == "__main__":
   print(solve())