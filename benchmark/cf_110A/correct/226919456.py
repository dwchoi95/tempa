x = input()
total = 0
for i in range(len(x)):
    if x[i] == '4' or x[i] == '7':
        total += 1
        if total > 7:
            break
if total == 4 or total == 7:
    print('YES')
else:
    print('NO')