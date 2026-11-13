if locals()['__file__'][-2:] == 'py': __import__('sys').stdin = open('in.txt', 'r')
from collections import defaultdict
rd = lambda: map(int, input().split())
n, m = rd()
d = defaultdict(int)
for x in rd():
    d[x] += 1
a = []
for x in d:
    a.append(d[x])
x = m // n
while x >= 1:
    t = 0
    for y in a:
        t += y // x
    if t >= n:
        break
    x -= 1
print(x)