N = list(input())

a = 0
b = 0

for k in N:
    if k == '4' or k == '7':
        a += 1
    else:
        b = 0

if a == len(N):
    print('YES')
else:
    print('NO')