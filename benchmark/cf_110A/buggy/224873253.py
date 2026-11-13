def is_lucky(num):
    # Check if a number is lucky (contains only 4s and 7s)
    while num > 0:
        digit = num % 10
        if digit != 4 and digit != 7:
            return False
        num //= 10
    return True

n = int(input())  # Input: The integer n

# Count the number of lucky digits (4 and 7) in n
lucky_count = 0
while n > 0:
    digit = n % 10
    if digit == 4 or digit == 7:
        lucky_count += 1
    n //= 10

# Check if the count of lucky digits is a lucky number
if is_lucky(lucky_count):
    print("YES")  # Output: n is a nearly lucky number
else:
    print("NO")   # Output: n is not a nearly lucky number