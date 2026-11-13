# Input
n = input()

# Count the number of lucky digits (4 and 7) in n
lucky_count = sum(1 for digit in n if digit in ['4', '7'])

# Check if the count is a lucky number
is_nearly_lucky = all(digit in ['4', '7'] for digit in str(lucky_count))

# Output the result
if is_nearly_lucky:
    print("YES")
else:
    print("NO")