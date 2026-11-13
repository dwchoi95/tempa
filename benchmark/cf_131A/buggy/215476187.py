# Read input
s = input()

# Check if the word should be converted
if s.isupper():
    s = s.lower()
elif len(s) > 1 and s[0].islower() and s[1:].isupper():
    s = s.capitalize()

# Print the result
print(s)