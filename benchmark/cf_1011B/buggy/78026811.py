n, m = map(int, input().split())
a = list(map(int, input().split()))
z = [0] * 101
t = 0
b = 0
for i in a:
    z[i] += 1
for i in range(1, m):
    t = 0
    for j in range(1, 101):
        t += z[j] // i
    if t >= n:
        b += 1
    else:
        break
print(b)