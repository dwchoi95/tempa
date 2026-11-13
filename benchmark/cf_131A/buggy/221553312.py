word = input()

# Check if the word meets the criteria for Caps Lock
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # Transform the word by toggling the case
    transformed_word = word.swapcase()
    print(transformed_word)
else:
    # If the criteria are not met, leave the word unchanged
    print(word)