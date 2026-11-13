def is_lucky_number(num):
    lucky_digits = ['4', '7']
    for digit in str(num):
        if digit not in lucky_digits:
            return False
    return True
def count_lucky_digits(num):
    count = 0
    for digit in str(num):
        if digit in ['4', '7']:
            count += 1
    return count
n = int(input())
lucky_digit_count = count_lucky_digits(n) 
if is_lucky_number(lucky_digit_count):
    print("YES")
else:
    print("NO")