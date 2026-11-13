s = input()

# Check if Caps Lock is turned on
if s.isupper() or (s[0].islower() and s[1:].isupper()):
    result = s.lower()
else:
    result = s

# Print the resulting string
print(result)