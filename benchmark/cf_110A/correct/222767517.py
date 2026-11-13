def is_lucky_number(n):
    return n == 4 or n == 7

def is_nearly_lucky_number(n):
    count = 0
    while n > 0:
        digit = n % 10
        if digit == 4 or digit == 7:
            count += 1
        n //= 10

    return is_lucky_number(count)

n = int(input().strip())

if is_nearly_lucky_number(n):
    print("YES")
else:
    print("NO")