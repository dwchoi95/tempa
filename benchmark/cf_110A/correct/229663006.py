inputNumber = int(input())

curLucky = 0
for number in str(inputNumber):
    if number in '47':
        curLucky += 1

if all(i in '47' for i in str(curLucky)):
    print('YES')
else:
    print('NO')