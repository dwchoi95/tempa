import math
num = int(input())

digLen = int(math.log10(num)+1)
c = 0
for i in range(digLen):
    if ((num % 10) in [4, 7]):
        num //= 10
        c += 1
    else:
        print("NO")
        break
if (digLen == c):
    print("YES")