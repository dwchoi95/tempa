def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_lucky_count(count):
    return count == 4 or count == 7

n = input()
lucky_count = 0

for digit in n:
    if is_lucky_digit(digit):
        lucky_count += 1

if is_lucky_count(lucky_count):
    print("YES")
else:
    print("NO")