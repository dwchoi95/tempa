num = input()
n = str(len(num))

for ele in n:
    if ele != '4' and ele != '7':
        print('NO')
        break
else:
    print('YES')