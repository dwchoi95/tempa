import math, sys
from collections import Counter, defaultdict, deque
from math import *
import heapq, bisect, itertools
print(math.sqrt(2), math.ceil(2.1), floor(-2.5), gcd(12, 18), math.pi, isqrt(17), math.log10(1000))
c = Counter("abracadabra")
print(c, c.most_common(2), c["z"])
d = defaultdict(list); d["a"].append(1); print(d, dict(d))
q = deque([1, 2]); q.appendleft(0); q.append(3); print(q.popleft(), q.pop(), q)
h = [5, 1, 4]; heapq.heapify(h); heapq.heappush(h, 0); print(heapq.heappop(h), h[0])
a = [1, 3, 3, 7]; print(bisect.bisect_left(a, 3), bisect.bisect_right(a, 3))
print(list(itertools.permutations([1, 2, 3], 2)), list(itertools.combinations("abc", 2)))
print(list(itertools.accumulate([1, 2, 3])), [(k, list(g)) for k, g in itertools.groupby("aabbbc")])
print(sys.maxsize, list(itertools.product([0, 1], repeat=2)))
