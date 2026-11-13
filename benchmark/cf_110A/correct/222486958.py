# Function to count the number of lucky digits (4 or 7) in a number
def count_lucky_digits(number):
    count = 0
    while number > 0:
        digit = number % 10
        if digit == 4 or digit == 7:
            count += 1
        number //= 10
    return count

# Read the input number
n = int(input())

# Count the lucky digits in the input number
lucky_digit_count = count_lucky_digits(n)

# Check if the count of lucky digits is itself a lucky number (4 or 7)
if lucky_digit_count == 4 or lucky_digit_count == 7:
    print("YES")
else:
    print("NO")