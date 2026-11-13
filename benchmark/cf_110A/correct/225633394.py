num = input()
based = []
for n in num:
    if n not in ['4', '7']:
        continue
    based.append(n)

n = str(len(based))

for ele in n:
    if ele != '4' and ele != '7':
        print('NO')
        break
else:
    print('YES')