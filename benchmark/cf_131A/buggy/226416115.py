# Read the input word
word = input()

# Check if the first character is uppercase and the rest are uppercase
if word[0].isupper() and word[1:].islower():
    # Convert the whole word to lowercase
    result = word.lower()
else:
    # Leave the word unchanged
    result = word

# Print the result
print(result)