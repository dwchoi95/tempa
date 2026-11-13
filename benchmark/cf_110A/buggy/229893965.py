number = input()


if '4' not in number or '7' not in number:
    print('NO')
    exit(0)

count = 0

for i in number:
    if i == '4' or i == '7':
        count += 1

if not (count % 4) or not (count % 7):
    print('YES')
else:
    print('NO')