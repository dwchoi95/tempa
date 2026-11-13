# Read the input word
word = input()

# Check if the Caps Lock rule should be applied
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # Apply the rule: toggle the case of all letters
    word = word.swapcase()

# Print the result
print(word)