import sys
import math

n = int(sys.stdin.readline())

d = int(round(n / float(3)))
print(int(d / 12), d % 12)