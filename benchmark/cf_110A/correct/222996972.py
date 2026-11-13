a = list(map(int, input()))

b = a.count(7)
c = a.count(4)
x = {4, 7}


if (b + c) in x:
    print('YES')
else:
    print('NO')