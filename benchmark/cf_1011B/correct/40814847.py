from collections import Counter


n, m = map(int, input().split())
d = list(Counter(map(int, input().split())).values())

for ans in range(1, 1000):
    if sum([x // ans for x in d]) < n:
        print(ans - 1)
        break