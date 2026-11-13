number = input()


if '4' not in number or '7' not in number:
    print('NO')
    exit(0)

count = 0

if (number.count('4') + number.count('7')) % 4 == 0 or number.count('4') + number.count('7') % 7 == 0:
    print('YES')
else:
    print('NO')