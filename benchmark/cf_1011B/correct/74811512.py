vis = [0 for _ in range(105)]
n, m = map(int, input().split())
for i in map(int, input().split()):
    vis[i] += 1
ans = 0
for i in range(1, m + 1):
    cnt = 0
    for j in range(1, 101):
        cnt += vis[j] // i
    if cnt >= n:
        ans = max(ans, i)
print(ans)