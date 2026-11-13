# Read the input word
s = input()

# Check if the entire word is uppercase
if s.isupper():
    # Convert the entire word to lowercase
    corrected_word = s.lower()
    
# Check if the first character is lowercase and all others are uppercase
elif s[0].islower() and s[1:].isupper():
    # Convert the first character to uppercase and the rest to lowercase
    corrected_word = s[0].upper() + s[1:].lower()
    
else:
    # No capitalization corrections needed
    corrected_word = s

# Print the corrected word
print(corrected_word)