n = int(input())

c = 0
for _ in range(len(str(n))):
    if n % 10 == 4 or n % 10 == 7:
        n = n//10
        c += 1

d = True
for _ in range(len(str(c))):
    if c % 10 == 4 or c % 10 == 7:
        c = c//10
    else:
        d = False
        break

if d: print('YES')
else: print('NO')