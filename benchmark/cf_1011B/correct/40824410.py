from collections import Counter
nop, nopkt = [int(x) for x in input().split()]
packets  = Counter([int(x) for x in input().split()]).values()
days = 1
while sum(x//days for x in packets) >= nop:
    days += 1
print(days - 1)