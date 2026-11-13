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
s = set()
arr = list(map(int, input().strip().split(" ")))
count = 0
for x in sorted(arr, reverse=True):
    count += 1
    if count == n:
        print(x)