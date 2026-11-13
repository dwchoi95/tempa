#Have copied from eugalt
from collections import Counter
n, m = list(map(int, input().split()))
a = [int(i) for i in input().split()]
d = dict(Counter(a)).values()  # {1: 4, 2: 3, 5: 2, 7: 1}
k = 1
while sum(i // k for i in d) >= n:
    k += 1
print(k - 1)