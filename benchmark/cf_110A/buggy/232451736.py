number = 0
n = input()
for i in range(len(n)):
    if str(n)[i] == '7' or str(n)[i] == '4':
        number += 1
if str(len(str(number))) in '47 74 444 447 474 477 744 747 774 777 4444 4447 \
4474 4477 4744 4747 4774 4777 7444':
    print('YES')
else:
    print('NO')