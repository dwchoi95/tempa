num = input()


count = 0

for n in num:
    if n in ['4', '7']:
        count += 1

if count in [4, 7]:
    print('YES')
else:
    print('NO')