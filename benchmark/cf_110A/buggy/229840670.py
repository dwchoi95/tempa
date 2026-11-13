li = list(input()); i = 0
for el in li:
    if el == '4' or '7':
        i += 1
t = list(str(i))
for el1 in t:
    if el1 == '4':
        print('YES')
        break
    elif el1 == '7':
        print('YES')
        break
    else:
        print('NO')
        break