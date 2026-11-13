n = input()
l = int(len(n))
c4 = int(n.count('4'))
c7 = int(n.count('7'))
if l - (c4 + c7) < c4 + c7:
    print('YES')
else:
    print('NO')