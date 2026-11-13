n = input()
count = 0
for i in range(len(n)):
    c = n[i]
    if c == '4' or c == '7':
        count += 1
    else:
        continue
if count == 4 or count == 7:
    print('YES')
else:
    print('NO')