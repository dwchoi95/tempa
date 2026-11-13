n = input()
l = int(len(n))
if l - int(n.count('4')) + int(n.count('7')) < int(n.count('4')) + int(n.count('7')) :
    print('YES')
else:
    print('NO')