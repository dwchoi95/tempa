import sys
def fastio():
    from io import StringIO
    from atexit import register
    global input
    sys.stdin = StringIO(sys.stdin.read())
    input = lambda : sys.stdin.readline().rstrip('\r\n')
    sys.stdout = StringIO()
    register(lambda : sys.__stdout__.write(sys.stdout.getvalue()))
fastio()

INF = 10**20
MOD = 10**9 + 7
I = lambda:list(map(int,input().split()))
from math import gcd
from math import ceil
from collections import defaultdict as dd, Counter
from bisect import bisect_left as bl, bisect_right as br

n, m = I()
a = I()
d = dd(int)
for i in a:
    d[i] += 1
ans = 0
for i in range(1000, 0, -1):
    p = 0
    for j in d:
        p += d[j] // i
    if p >= n:
        ans = i
        break
print(ans)