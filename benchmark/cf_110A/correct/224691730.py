num = input()
l1 = len(num)
count = 0
for x in range(l1):
    if num[x] == '4':
        count += 1
    elif num[x] == '7':
        count += 1
if count == 4:
    print('YES')
elif count == 7:
    print('YES')
else:
    print('NO')