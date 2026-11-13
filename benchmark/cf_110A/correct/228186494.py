def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_lucky_number(number):
    return all(is_lucky_digit(digit) for digit in str(number))

n = int(input())
lucky_count = str(n).count('4') + str(n).count('7')

if is_lucky_number(lucky_count):
    print("YES")
else:
    print("NO")