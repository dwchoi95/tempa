data = input()
num4 = data.count('4')
num7 = data.count('7')

total = str(num4 + num7)

if total == '0':
    print('NO')
elif total.count('4') + total.count('7') == len(total):
    print('YES')
else:
    print('NO')