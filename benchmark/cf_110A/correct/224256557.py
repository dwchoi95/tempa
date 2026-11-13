n = int(input())

if str(n).count('4') + str(n).count('7') == 4 or str(n).count('4') + str(n).count('7') == 7:
    print('YES')
else:
    print('NO')