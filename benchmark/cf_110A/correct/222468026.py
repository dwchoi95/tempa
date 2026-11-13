n = input()

if len(n) < 4:
    print('NO')
else:
    lucky_count = 0

    for c in n:
        if c == '4' or c == '7':
            lucky_count += 1

    if lucky_count == 4 or lucky_count == 7:
        print('YES')
    else:
        print('NO')