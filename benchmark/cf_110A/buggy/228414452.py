a = input()
for i in range(len(a)):
    if a[i] in '47':
        continue
    else:
        print('NO')
        exit(0)
if a.count('4') + a.count('7') == 4 or a.count('4') + a.count('7') == 7:
    print('YES')
else:
    print('NO')