n = list(input())
happy_nums = 0

for num in n:
    if num == '4' or num == '7':
        happy_nums += 1

if happy_nums == 4 or happy_nums == 7:
    print('YES')
else:
    print('NO')