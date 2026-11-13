def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_nearly_lucky(n):
    count_lucky_digits = 0
    while n > 0:
        digit = n % 10
        if is_lucky_digit(str(digit)):
            count_lucky_digits += 1
        n //= 10
    
    return is_lucky_digit(str(count_lucky_digits))

n = int(input())
print("YES") if is_nearly_lucky(n) else print("NO")