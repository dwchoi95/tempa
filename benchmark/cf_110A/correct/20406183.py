n = int(input())

k = 0

ch = [4, 7, 44, 47, 74, 77, 444, 447, 474, 477, 744, 747, 774, 777]

while n > 0:

    t = n % 10

    if t == 4 or t == 7:

        k += 1

    n //= 10



if k in ch:

    print('YES')

else:

    print('NO')