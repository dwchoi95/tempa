n = str(input())
integers = list(n)
count = 0

for i in range(len(integers)):
    if integers[i] == '4' or integers[i] == '7':
        count += 1

if count == 4 or count == 7:
    print('YES')
else:
    print('NO')