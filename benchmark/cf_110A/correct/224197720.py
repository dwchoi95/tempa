n = input()
c = int(n.count('4')) + int(n.count('7'))
if c != 0 and c == 4 or c == 7:
    print('YES')
else:
    print('NO')