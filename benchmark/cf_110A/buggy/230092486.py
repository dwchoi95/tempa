def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_lucky_number(n):
    count = 0
    for digit in str(n):
        if is_lucky_digit(digit):
            count += 1

    return is_lucky_digit(str(count))

# Input number to check if it's a nearly lucky number
n = int(input("Enter a number:"))

if is_lucky_number(n):
    print(f"{n} is a nearly lucky number.")
else:
    print(f"{n} is not a nearly lucky number.")