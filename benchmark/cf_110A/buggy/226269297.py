n = input()

# Count the lucky digits (4 and 7) in the number
lucky_count = n.count('4') + n.count('7')

# Check if the count of lucky digits is itself a lucky number
lucky_digits = str(lucky_count)
if all(digit in '47' for digit in lucky_digits):
    print("YES")
else:
    print("YES")