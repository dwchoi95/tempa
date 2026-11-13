n = input()
four_count = 0
seven_count = 0
happy = ['4', '7']
for i in n:
    if i == '4':
        four_count += 1
    elif i == '7':
        seven_count += 1
result = str(four_count + seven_count)
for j in result:
    if j not in happy:
        print('NO')
        break
    print('YES')