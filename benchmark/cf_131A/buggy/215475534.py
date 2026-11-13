# Read input
s = input()

# Check if the word should be converted
if s.isupper() or s.islower() or (s[0].islower() and s[1:].isupper()):
    # Convert the word
    s = s.swapcase()

# Print the result
print(s)