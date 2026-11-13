def fix_caps_lock(word):
    # Check if the word only contains uppercase letters or all letters except the first one are uppercase
    if word.isupper() or (word[0].islower() and word[1:].isupper()):
        # Change the case of all letters in the word
        return word.swapcase()
    else:
        # Return the word unchanged
        return word

# Input a word
word = input()

# Apply the fix_caps_lock function
fixed_word = fix_caps_lock(word)

# Print the fixed word
print(fixed_word)