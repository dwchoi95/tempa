import math
num = int(input())

digLen = int(math.log10(num)+1)
flag = 1
for i in range(digLen):
    rem = num % 10
    num //= 10
    if (rem in [4, 7]):
        continue
    elif (digLen not in [4, 7]):
        flag = -1

if (flag == 1):
    print("YES")
else:
    print("NO")