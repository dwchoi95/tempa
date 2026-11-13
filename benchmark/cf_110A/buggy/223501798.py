x = input()
numbers = []
a = 0
for i in range(len(x)):
    numbers.append(x[i])
while '4' in numbers:
    numbers.remove('4')
    a += 1
while '7' in numbers:
    numbers.remove('7')
    a += 1
if a%4 == 0 or a%7 == 0:
    print('YES')
else:
    print('NO')