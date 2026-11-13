from collections import Counter
m,n = map(int, input().split())
r = Counter(list(map(int, input().split()))).values()
#print(r)
i = 1
while sum(x//i for x in r)>=m:
    i+=1
print(i-1)