def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def is_lucky_count(count):
    return all(digit in '47' for digit in str(count))

n = int(input())
count = 0

# Count the lucky digits in n
for digit in str(n):
    if is_lucky_digit(digit):
        count += 1

# Check if the count is a lucky number
if is_lucky_count(count):
    print("YES")
else:
    print("NO")