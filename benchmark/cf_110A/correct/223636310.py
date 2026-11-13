def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def count_lucky_digits(number):
    count = 0
    for digit in str(number):
        if is_lucky_digit(digit):
            count += 1
    return count

def is_lucky(num):
    return num == 4 or num == 7

def is_nearly_lucky(number):
    lucky_digit_count = count_lucky_digits(number)
    return is_lucky(lucky_digit_count)

# Main code
n = input().strip()
if is_nearly_lucky(n):
    print("YES")
else:
    print("NO")