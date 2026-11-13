n = input()
sum = 0
for i in range(len(n)):
    if '4' in n or '7' in n:
        sum += 1
    else:
        sum += 0
if sum == 4 or sum == 7:
    print('YES')
else:
    print('NO')