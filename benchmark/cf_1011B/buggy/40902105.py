[n, m] = map(int, input().split())
data = list(map(int, input().split()))
cnt = [0] * 12
for i in data:
    cnt[i] += 1
for i in range(1, len(cnt))[::-1]:
    cnt[i - 1] += cnt[i]

max = 0
for i in range(0, len(cnt)):
    if cnt[i] > n:
        max = i
print(max)