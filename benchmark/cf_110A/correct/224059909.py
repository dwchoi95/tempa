def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_lucky_number(number):
    return all(is_lucky_digit(digit) for digit in number)

def is_nearly_lucky_number(n):
    lucky_digit_count = 0
    while n > 0:
        digit = n % 10
        if is_lucky_digit(str(digit)):
            lucky_digit_count += 1
        n //= 10

    return is_lucky_number(str(lucky_digit_count))

# Read input
n = int(input())

# Check if n is a nearly lucky number
if is_nearly_lucky_number(n):
    print("YES")
else:
    print("NO")