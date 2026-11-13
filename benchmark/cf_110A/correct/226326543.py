def is_lucky(num):
    # Count the number of lucky digits (4 and 7) in the number
    count = 0
    while num > 0:
        digit = num % 10
        if digit == 4 or digit == 7:
            count += 1
        num //= 10

    # Check if the count of lucky digits is itself a lucky number (4 or 7)
    return count == 4 or count == 7

def is_nearly_lucky(n):
    # Check if n is a nearly lucky number
    if is_lucky(n):
        return "YES"
    else:
        return "NO"

# Read the input
n = int(input())

# Check if n is a nearly lucky number and print the result
print(is_nearly_lucky(n))