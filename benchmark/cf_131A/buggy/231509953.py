word = input()

# Check if the Caps lock rule applies
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # If yes, change the case of all letters
    print(word.swapcase())
else:
    # Otherwise, leave the word unchanged
    print(word)