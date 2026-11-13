import sys
n, m = list(map(int, input().split()))
q = []
c = []
for i in range(101):
    q.append(0)
a = list(map(int, input().split()))
for i in range(m):
    q[a[i]]+=1
for i in range(100):
    d = 100 - i
    k = 0
    for j in range(100):
        if q[j+1] >= d:
            k += q[j+1]//d
    if k >= n:
        print(d)
        exit()
print(0)