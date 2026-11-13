def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def count_lucky_digits(number):
    return sum(1 for digit in str(number) if is_lucky_digit(digit))

def is_nearly_lucky_number(n):
    lucky_digit_count = count_lucky_digits(n)
    return is_lucky_digit(str(lucky_digit_count))

n = int(input().strip())
if is_nearly_lucky_number(n):
    print("YES")
else:
    print("NO")