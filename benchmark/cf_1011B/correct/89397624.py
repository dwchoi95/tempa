n, m = [int(i) for i in input().split()]
a = [int(i) for i in input().split()]

food = [0] * 100
for i in a:
    food[i - 1] += 1


max_amount = 0
for i in range(1, m+1):
    sub_food = food.copy()
    sub_n = n

    for j in range(100):
        while sub_food[j] >= i and sub_n > 0:
            sub_food[j] -= i
            sub_n -= 1
        if sub_n == 0:
            break

    if sub_n == 0:
        max_amount = i

print(max_amount)