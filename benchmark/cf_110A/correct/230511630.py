n = int(input())  # Read the input number

# Count the number of lucky digits (4 and 7)
lucky_count = str(n).count('4') + str(n).count('7')

# Check if the count is a lucky number (4 or 7)
if lucky_count == 4 or lucky_count == 7:
    print("YES")
else:
    print("NO")