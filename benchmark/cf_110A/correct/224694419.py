def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def count_lucky_digits(number):
    count = 0
    while number > 0:
        digit = str(number % 10)
        if is_lucky_digit(digit):
            count += 1
        number //= 10
    return count

def is_nearly_lucky_number(n):
    lucky_digit_count = count_lucky_digits(n)
    return is_lucky_digit(str(lucky_digit_count))

n = int(input())
if is_nearly_lucky_number(n):
    print("YES")
else:
    print("NO")