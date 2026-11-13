li = list(input()); i = 0
for el in li:
    if el == '4' or '7':
        i += 1
for el1 in list(str(i)):
    if el1 != '4' or '7':
        print('NO')
        break
    else:
        print('YES')
        break