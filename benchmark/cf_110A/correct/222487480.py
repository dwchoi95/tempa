def count_lucky_digits(number):
    count = 0
    while number > 0:
        digit = number % 10
        if digit == 4 or digit == 7:
            count += 1
        number //= 10
    return count
n = int(input())
lucky_digit_count = count_lucky_digits(n)
if lucky_digit_count == 4 or lucky_digit_count == 7:
    print("YES")
else:
    print("NO")