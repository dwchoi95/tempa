def is_nearly_lucky(n):
    lucky_digits = [4, 7]  # Lucky digits
    count = 0

    # Count the number of lucky digits in n
    while n > 0:
        digit = n % 10
        if digit in lucky_digits:
            count += 1
        n //= 10

    # Check if count is a lucky number
    if count == 4 or count == 7:
        return "YES"
    else:
        return "NO"

n = int(input())
result = is_nearly_lucky(n)
print(result)