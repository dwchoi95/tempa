def count_lucky_digits(qt):
    count = 0
    while qt > 0:
        digit =qt % 10
        if digit == 4 or digit == 7:
            count += 1
        qt //= 10
    return count

def lucky_num(n):
    return n == 4 or n == 7

def is_nearly_lucky(qt):
    digit_count = count_lucky_digits(qt)
    return lucky_num(digit_count)

qt = int(input())

if is_nearly_lucky(qt):
    print("YES")
else:
    print("NO")