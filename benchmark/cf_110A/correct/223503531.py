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

a_ = []
b = str(a)
for i in range(len(b)):
    a_.append(b[i])
while '4' in a_:
    a_.remove('4')
while '7' in a_:
    a_.remove('7')
if a != 0:
    if a_:
        print('NO')
    else:
        print('YES')
elif a == 0:
    print('NO')