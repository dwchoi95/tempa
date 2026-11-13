# Read input
s = input()

# Check if the word should be converted
if s.isupper() or s[1:].islower():
    # Convert the word
    s = s.swapcase()

# Print the result
print(s)