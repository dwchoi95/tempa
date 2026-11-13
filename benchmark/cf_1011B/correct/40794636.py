n, k = map(int, input().split())
arr = list(map(int, input().split()))
#print(arr)
l = 0
r = 1000
while (l < r - 1):
    #print(l, r)
    cur = (l + r) // 2
    counts = [0] * 101
    #print(*counts)
    for el in arr:
        counts[el] += 1
    res = 1
    #print(*counts)
    for i in range(n):
        ab = 0
        for j in range(101):
            if (counts[j] >= cur and ab == 0):
                counts[j] -= cur
                ab = 1
                break
                #res = 1
        if ab == 0:
            res = 0
    if res == 0:
        r = cur
    else:
        l = cur
print(l)