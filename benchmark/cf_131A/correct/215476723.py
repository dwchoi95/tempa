# Read input
n = input()

# Check if the word should be converted
if n[1:].upper() == n[1:]:
    result = n.swapcase()
else:
    result = n

# Print the result
print(result)