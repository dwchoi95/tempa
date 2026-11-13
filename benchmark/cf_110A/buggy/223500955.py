x = input()
numbers = []
for i in range(len(x)):
    numbers.append(x[i])
while '4' in numbers:
    numbers.remove('4')
while '7' in numbers:
    numbers.remove('7')
if numbers:
    print('NO')
else:
    print('YES')