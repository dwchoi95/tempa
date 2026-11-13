import sys
import math
def result(N):
    if (N < 4):
        return False
    while (N > 0):
        if (N % 10 != 4 and N % 10 != 7):
            return False
        N = N // 10
    return True
N = int(input())
count = 0
while (N > 0):
    if (N % 10 == 4 or N % 10 == 7):
        count = count + 1
    N = N // 10
if (result(count)):
    print("YES")
else:
    print("NO")