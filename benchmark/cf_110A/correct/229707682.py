def is_lucky_number(num):
    return num == 4 or num == 7

def count_lucky_digits(num):
    count = 0
    while num > 0:
        digit = num % 10
        if digit == 4 or digit == 7:
            count += 1
        num //= 10
    return count

n = int(input())

lucky_digit_count = count_lucky_digits(n)

if is_lucky_number(lucky_digit_count):
    print("YES")
else:
    print("NO")