from collections import Counter

n, m = list(map(int, input().split()))
food = sorted([(q, t) for t, q in Counter(list(map(int, input().split()))).items()])

def ration(n, f, t):
    result = 0
    for q, _ in f:
        result += q//t
    if result < n: return 0
    else: return 1

days = 0
while ration(n, food, days+1):
    days += 1

print(days)