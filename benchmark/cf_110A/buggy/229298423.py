n = input()


fortunato = True
for char in n:
    if char != '7' or char != '4':
        fortunato = True

if fortunato:
    print('YES')
else:
    print('NO')