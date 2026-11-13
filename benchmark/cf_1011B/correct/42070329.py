#codeforces_1011B
gi = lambda: list(map(int,input().split()))
n,m = gi()
l = [0]*101
for e in gi():
        l[e] += 1
k = 1
while sum([e//k for e in l]) >= n:
        k += 1
print(k-1)