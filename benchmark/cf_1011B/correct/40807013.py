def proverka(k, n):
    kol = 0
    i = 0
    while i < len(count) and kol < n:
        kol += count[i] // k
        i += 1
    return kol >= n


n, m = map(int, input().split())
myList = list(map(int, input().split()))
count = [0] * 101
for elem in myList:
    count[elem] += 1
s = sum(count)
if s < n:
    print(0)
else:
    k = 1
    new_k = 2
    count.sort(reverse=True)
    while True:
        if proverka(new_k, n):
            k = new_k
            new_k = k + 1
        else:
            break
    print(k)