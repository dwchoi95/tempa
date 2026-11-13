n, m = map(int, input().split(' '))
arr = list(map(int, input().split(' ')))

d = dict()
for i in range(m):
    if d.get(arr[i]) is not None:
        d[arr[i]]+=1
    else:
        d[arr[i]] = 1

ans = 0
prev = -1
for i in range(1, 10000):
    val = 0
    prev = ans
    for k in d.keys():
        val = val+d[k]//i
        if val>=n:
            ans = i
            break
    if ans==prev:
        break
print(ans)