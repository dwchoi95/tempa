from collections import defaultdict


def fun(mid):
    cnt = 0
    for x in arr_set:
        cnt += (freq[x]) // mid
    return cnt >= n


n, m = map(int, input().split())
arr = list(map(int, input().split()))
freq = defaultdict(int)
for x in arr:
    freq[x] += 1
arr_set = set(arr)
start = 1
end = m
ans = -1
while(start <= end):
    mid = (start + end) // 2
    if(fun(mid)):
        ans = mid
        start = mid + 1
    else:
        end = mid - 1
if(ans == -1):
    print(0)
else:
    print(ans)