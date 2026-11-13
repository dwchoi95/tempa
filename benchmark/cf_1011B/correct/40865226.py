from collections import*
n, m = map(int, input().split())
a = Counter(map(int, input().split())).values()
i = 1
while sum(x // i for x in a) >= n:
    i += 1
print(i - 1)