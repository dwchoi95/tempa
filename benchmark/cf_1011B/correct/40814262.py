def getWeight(a):
    return(ord(a) - ord('a')+1)

n,m = input().strip().split(" ")
n = int(n)
m = int(m)
if (m < n):
    print("0")
    exit(0)
if (n <= 0):
    print("0")
    exit(0)
if (m <= 0):
    print("0")
    exit(0)
d = {}
arr = list(map(int, input().strip().split(" ")))
for x in arr:
    try:
        d[x] += 1
    except KeyError:
        d[x] = 1
arr =sorted(d.values(), reverse=True)

ret = 0
for i in range(1, arr[0]+1):
    count = 0
    for x in arr:
        count += int(int(x)/int(i))
        if count >= n:
            ret = i
            break
print(ret)