word = input()

# Check if the word satisfies the Caps lock condition
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # If yes, change the case of all letters
    print(word.swapcase())
else:
    # If not, leave the word unchanged
    print(word)