# Read the input number as a string
n = input().strip()

# Count the number of lucky digits (4 and 7) in the input string
lucky_count = n.count('4') + n.count('7')

# Check if the count of lucky digits is a lucky number (4 or 7)
if lucky_count == 4 or lucky_count == 7:
    print("YES")
else:
    print("NO")