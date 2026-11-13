#k = int(input())
import sys
n, m = map(int, input().split())
a = list(map(int, input().split()))
#a = input()
a.sort()
b = [1]
for i in range(1, len(a)):
    if( a[i] == a[i-1] ):
        b[-1] += 1
    else:
        b.append( 1 )
b.sort(reverse=True)
kol = 0
flag = True
for i in range(100, 0, -1):
    for j in range(len(b)):
        kol += b[j] // i
    if( kol >= n ):
        print(i)
        flag = False
        break
    kol = 0
if flag:
    print(0)