num = input()
lucky = num.count('4')+num.count('7')
if lucky == 4 or lucky == 7:
    print('YES')
else:
    print('NO')