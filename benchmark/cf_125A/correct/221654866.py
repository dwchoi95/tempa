#n = map(int, input().split())
n = int(input())
duim = n // 3
if n - (duim*3) == 2:
    duim += 1

fut = duim // 12
duim = duim - (fut*12)
print(fut, duim)