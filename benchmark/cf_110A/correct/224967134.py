def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def count_lucky_digits(n):
    count = 0
    while n > 0:
        if is_lucky_digit(str(n % 10)):
            count += 1
        n //= 10
    return count

def is_lucky_number(n):
    return n == 4 or n == 7

def is_nearly_lucky_number(n):
    lucky_digit_count = count_lucky_digits(n)
    return is_lucky_number(lucky_digit_count)

def main():
    n = int(input())
    if is_nearly_lucky_number(n):
        print('YES')
    else:
        print("NO")

if __name__ == "__main__":
    main()