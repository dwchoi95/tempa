x = int(input())
k = 0
i = 1

while k < x:
    k += i
    i += 1

while (k - x) % 2 != 0:
    k += i
    i += 1

print(i-1)