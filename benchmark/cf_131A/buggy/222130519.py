# Read the input word
word = input()

# Check if the word should have its case changed
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    result = word.swapcase()
else:
    result = word

# Print the result
print(result)