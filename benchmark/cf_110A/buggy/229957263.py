data = input()
num4 = data.count('4')
num7 = data.count('7')

total = num4 + num7
if total == len(data):
    print('YES')
elif total == 0:
    print('NO')
elif total % 4 == 0 or total % 7 == 0:
    print('YES')
else:
    print('NO')