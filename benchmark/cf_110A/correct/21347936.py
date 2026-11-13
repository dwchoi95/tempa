s = input()
counter = 0
for char in s:
    if char == '4' or char == '7':
        counter += 1
if counter == 4 or counter == 7:
    print('YES')
else:
    print('NO')