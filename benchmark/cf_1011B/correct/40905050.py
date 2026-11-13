[n, m] = map(int, input().split())
data = list(map(int, input().split()))
cnt = [0] * 120
for i in data:
    cnt[i] += 1

ans = 0
i = 1
while True:
    ans = 0
    for j in cnt:
        ans += j//i
    if ans < n:
        print(i-1)
        break;
    i += 1