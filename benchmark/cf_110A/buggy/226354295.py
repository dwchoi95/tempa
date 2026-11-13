sat = set()
lis = []
x = input()
counter = 0
for i in x:
    if i == '4' or i == '7':
        counter += 1
    sat.add(i)
    lis.append(i)
if sat == {'4', '7'} or sat == {'7', '4'}:
    print('YES')
elif counter == 4 or counter == 7:
    print('YES')
else:
    print('NO')