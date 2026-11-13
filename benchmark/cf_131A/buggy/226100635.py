# Read the input word
word = input()

# Check if the word should be modified
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # Convert the word to the opposite case
    modified_word = word.swapcase()
else:
    # Leave the word unchanged
    modified_word = word

# Print the result
print(modified_word)