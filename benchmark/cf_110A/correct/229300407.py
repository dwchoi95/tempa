n = input()

fortunato = False
count = 0

if int(n) > 9:
    for char in n:
        if int(char) == 7 or int(char) == 4:
            count += 1

if count == 7 or count == 4:
    print('YES')
else:
    print('NO')