n = input()
c = int(n.count('4')) + int(n.count('7'))
if c % 4 == 0 or c % 7 == 0:
    print('YES')
else:
    print('NO')