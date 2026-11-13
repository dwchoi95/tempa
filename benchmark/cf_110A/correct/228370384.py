# Read the input number as a string
n = input()

# Count the number of lucky digits (4 and 7)
count = n.count('4') + n.count('7')

# Check if the count is a lucky number (4 or 7)
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")