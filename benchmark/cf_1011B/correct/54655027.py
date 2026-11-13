from collections import Counter

n, _ = map(int,input().split())

c = Counter(list(map(int,input().split())))

result = 0
res = 1

while True:
    result = 0
    for i in c.values():
        result += (i//res)
    if result < n:
        res-=1
        break
    res +=1

print(res)