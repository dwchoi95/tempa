n, m = map(int, input().split())
a = list(map(int, input().split()))
vis = [0 for i in range(105)]
for i in range(m):
    vis[a[i]] += 1
ans = 0
for i in range(1, m + 1):
    cnt = 0
    for j in range(1, 101):
        cnt += vis[j] // i
    if cnt >= n:
        ans = max(ans, i)
print(ans)