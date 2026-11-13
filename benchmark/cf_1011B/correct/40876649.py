n, m = map(int, input().split())

c = [0 for i in range(110)]

for el in input().split():
    c[int(el)] += 1
ans = 100

for i in range(100, 0, -1):
    t = n
    for j in range(1, 102):
        t -= c[j] // i
    if t <= 0:
        print(i)
        exit(0)
print(0)