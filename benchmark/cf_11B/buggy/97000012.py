x = int(input())
s = 0
n = 0
while s != x:
    n += 1
    if s + n <= x:
        s += n
    else:
        s -= n
print(n)