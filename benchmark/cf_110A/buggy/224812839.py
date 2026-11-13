def is_lucky_digit(digit):
    return digit == 4 or digit == 7

def is_nearly_lucky_number(n):
    lucky_digit_count = 0

    # Count the lucky digits (4 and 7) in the number
    while n > 0:
        digit = n % 10
        if is_lucky_digit(digit):
            lucky_digit_count += 1
        n //= 10

    # Check if the count of lucky digits is a lucky number
    return lucky_digit_count == 0 or lucky_digit_count % 4 == 0 or lucky_digit_count % 7 == 0

if __name__ == "__main__":
    n = int(input().strip())
    if is_nearly_lucky_number(n):
        print("YES")
    else:
        print("NO")