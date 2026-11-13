import sys
from itertools import permutations
import collections
import math
M = 1000000007

n = (int(sys.stdin.readline()))
#a = list(map(int,sys.stdin.readline().split()))

a = collections.Counter(str(n))
if "7" not in a.keys() or "4" not in a.keys():
    print("NO")
elif a["7"] + a["4"] != 4 and a["7"] + a["4"] != 7:
    print("NO")
elif a["7"] + a["4"] != 7 and a["7"] + a["4"] != 4:
    print("NO")
else: print("YES")