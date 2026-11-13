x = input()
if len(x) == 1 and x != '7' and x != '4':
    print('NO')
    exit()
else:
    print('YES')
for i in x:
    if i != '7' and i != '4':
        print('NO')
        exit()
print('YES')