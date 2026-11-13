word = input()

# Check if the word meets the criteria for Caps Lock being accidentally switched on
if word.isupper() or (word[0].islower() and word[1:].isupper()):
    # If so, change the case of all letters
    res = word.swapcase()
else:
    # Otherwise, leave the word unchanged
    res = word

print(res)